// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedLemmas
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Basic import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred import Lean.Meta.AppBuilder import Std.Tactic.BVDecide.Reflect
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
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lemma_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "cond_true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(71, 253, 9, 241, 22, 101, 244, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cond_false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 177, 250, 0, 252, 101, 138, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(lean_object* v_expr_2_, lean_object* v_a_3_, lean_object* v_lhs_4_, lean_object* v_lemmaName_5_, lean_object* v___x_6_, lean_object* v_discrExpr_7_, lean_object* v_lhsExpr_8_, lean_object* v_rhsExpr_9_, lean_object* v___x_10_, lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v___x_13_, lean_object* v___x_14_, lean_object* v___x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_2_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
if (lean_obj_tag(v___x_25_) == 0)
{
lean_object* v_a_26_; lean_object* v___x_27_; 
v_a_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc(v_a_26_);
lean_dec_ref_known(v___x_25_, 1);
v___x_27_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_a_3_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_47_; 
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_47_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_47_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_47_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___y_33_; 
if (lean_obj_tag(v_a_28_) == 0)
{
lean_object* v___x_45_; 
lean_inc(v_a_26_);
v___x_45_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_26_);
v___y_33_ = v___x_45_;
goto v___jp_32_;
}
else
{
lean_object* v_val_46_; 
v_val_46_ = lean_ctor_get(v_a_28_, 0);
lean_inc(v_val_46_);
lean_dec_ref_known(v_a_28_, 1);
v___y_33_ = v_val_46_;
goto v___jp_32_;
}
v___jp_32_:
{
lean_object* v_width_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v_width_34_ = lean_ctor_get(v_lhs_4_, 0);
lean_inc(v_width_34_);
lean_dec_ref(v_lhs_4_);
lean_inc(v___x_6_);
v___x_35_ = l_Lean_mkConst(v_lemmaName_5_, v___x_6_);
v___x_36_ = l_Lean_mkNatLit(v_width_34_);
v___x_37_ = l_Lean_mkApp4(v___x_35_, v___x_36_, v_discrExpr_7_, v_lhsExpr_8_, v_rhsExpr_9_);
v___x_38_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0));
v___x_39_ = l_Lean_Name_mkStr6(v___x_10_, v___x_11_, v___x_12_, v___x_13_, v___x_14_, v___x_38_);
v___x_40_ = l_Lean_mkConst(v___x_39_, v___x_6_);
v___x_41_ = l_Lean_mkApp4(v___x_40_, v___x_15_, v_a_26_, v___y_33_, v___x_37_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v___x_41_);
v___x_43_ = v___x_30_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
else
{
lean_object* v_a_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_55_; 
lean_dec(v_a_26_);
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
v_a_48_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_55_ == 0)
{
v___x_50_ = v___x_27_;
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_a_48_);
lean_dec(v___x_27_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_55_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
lean_object* v___x_53_; 
if (v_isShared_51_ == 0)
{
v___x_53_ = v___x_50_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v_a_48_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
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
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_56_ = _args[0];
lean_object* v_a_57_ = _args[1];
lean_object* v_lhs_58_ = _args[2];
lean_object* v_lemmaName_59_ = _args[3];
lean_object* v___x_60_ = _args[4];
lean_object* v_discrExpr_61_ = _args[5];
lean_object* v_lhsExpr_62_ = _args[6];
lean_object* v_rhsExpr_63_ = _args[7];
lean_object* v___x_64_ = _args[8];
lean_object* v___x_65_ = _args[9];
lean_object* v___x_66_ = _args[10];
lean_object* v___x_67_ = _args[11];
lean_object* v___x_68_ = _args[12];
lean_object* v___x_69_ = _args[13];
lean_object* v___y_70_ = _args[14];
lean_object* v___y_71_ = _args[15];
lean_object* v___y_72_ = _args[16];
lean_object* v___y_73_ = _args[17];
lean_object* v___y_74_ = _args[18];
lean_object* v___y_75_ = _args[19];
lean_object* v___y_76_ = _args[20];
lean_object* v___y_77_ = _args[21];
lean_object* v___y_78_ = _args[22];
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(v_expr_56_, v_a_57_, v_lhs_58_, v_lemmaName_59_, v___x_60_, v_discrExpr_61_, v_lhsExpr_62_, v_rhsExpr_63_, v___x_64_, v___x_65_, v___x_66_, v___x_67_, v___x_68_, v___x_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
return v_res_79_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_box(0);
v___x_86_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2));
v___x_87_ = l_Lean_mkConst(v___x_86_, v___x_85_);
return v___x_87_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_box(0);
v___x_98_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8));
v___x_99_ = l_Lean_mkConst(v___x_98_, v___x_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(lean_object* v_discr_113_, lean_object* v_atom_114_, lean_object* v_lhs_115_, lean_object* v_discrExpr_116_, lean_object* v_atomExpr_117_, lean_object* v_lhsExpr_118_, lean_object* v_rhsExpr_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0));
v___x_128_ = lean_box(0);
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3);
lean_inc_ref(v_discrExpr_116_);
v___x_130_ = l_Lean_Expr_app___override(v___x_129_, v_discrExpr_116_);
v___x_131_ = l_Lean_Meta_Sym_shareCommonInc(v___x_130_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_133_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_n(v_a_132_, 2);
lean_dec_ref_known(v___x_131_, 1);
lean_inc_ref(v_discrExpr_116_);
v___x_133_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_discr_113_, v_discrExpr_116_, v_a_132_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6));
v___x_136_ = lean_unsigned_to_nat(2u);
v___x_137_ = lean_mk_empty_array_with_capacity(v___x_136_);
lean_inc_ref(v_atomExpr_117_);
v___x_138_ = lean_array_push(v___x_137_, v_atomExpr_117_);
lean_inc_ref(v_lhsExpr_118_);
v___x_139_ = lean_array_push(v___x_138_, v_lhsExpr_118_);
v___x_140_ = l_Lean_Meta_mkAppM(v___x_135_, v___x_139_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = l_Lean_Meta_Sym_shareCommonInc(v_a_141_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; uint8_t v___x_144_; lean_object* v___x_145_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc_n(v_a_143_, 2);
lean_dec_ref_known(v___x_142_, 1);
v___x_144_ = 0;
lean_inc_ref(v_lhsExpr_118_);
lean_inc_ref(v_lhs_115_);
v___x_145_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_atom_114_, v_lhs_115_, v_atomExpr_117_, v_lhsExpr_118_, v___x_144_, v_a_143_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_211_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_211_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_211_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_211_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
if (lean_obj_tag(v_a_146_) == 1)
{
lean_object* v_val_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_206_; 
lean_del_object(v___x_148_);
v_val_150_ = lean_ctor_get(v_a_146_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v_a_146_);
if (v_isSharedCheck_206_ == 0)
{
v___x_152_ = v_a_146_;
v_isShared_153_ = v_isSharedCheck_206_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_val_150_);
lean_dec(v_a_146_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_206_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_150_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9);
lean_inc(v_a_143_);
lean_inc(v_a_132_);
v___x_157_ = l_Lean_mkAppB(v___x_156_, v_a_132_, v_a_143_);
lean_inc_ref(v___x_157_);
v___x_158_ = l_Lean_Meta_Sym_shareCommonInc(v___x_157_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; uint8_t v___x_160_; lean_object* v___x_161_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
v___x_160_ = 3;
v___x_161_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_a_134_, v_a_155_, v_a_132_, v_a_143_, v___x_160_, v_a_159_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_, v_a_125_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_181_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_181_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_181_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_181_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v_bvExpr_166_; lean_object* v_expr_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_lemmaName_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v_bvExpr_166_ = lean_ctor_get(v_a_162_, 0);
lean_inc_ref(v_bvExpr_166_);
v_expr_167_ = lean_ctor_get(v_a_162_, 3);
lean_inc_ref_n(v_expr_167_, 2);
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10));
v___x_169_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11));
v___x_170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12));
v___x_171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13));
v_lemmaName_172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16));
v___f_173_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed), 23, 14);
lean_closure_set(v___f_173_, 0, v_expr_167_);
lean_closure_set(v___f_173_, 1, v_a_162_);
lean_closure_set(v___f_173_, 2, v_lhs_115_);
lean_closure_set(v___f_173_, 3, v_lemmaName_172_);
lean_closure_set(v___f_173_, 4, v___x_128_);
lean_closure_set(v___f_173_, 5, v_discrExpr_116_);
lean_closure_set(v___f_173_, 6, v_lhsExpr_118_);
lean_closure_set(v___f_173_, 7, v_rhsExpr_119_);
lean_closure_set(v___f_173_, 8, v___x_168_);
lean_closure_set(v___f_173_, 9, v___x_169_);
lean_closure_set(v___f_173_, 10, v___x_170_);
lean_closure_set(v___f_173_, 11, v___x_171_);
lean_closure_set(v___f_173_, 12, v___x_127_);
lean_closure_set(v___f_173_, 13, v___x_157_);
v___x_174_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_174_, 0, v_bvExpr_166_);
lean_ctor_set(v___x_174_, 1, v___f_173_);
lean_ctor_set(v___x_174_, 2, v_expr_167_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_174_);
v___x_176_ = v___x_152_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_180_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_178_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_176_);
v___x_178_ = v___x_164_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_176_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v___x_157_);
lean_del_object(v___x_152_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
v_a_182_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_161_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_161_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
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
lean_dec_ref(v___x_157_);
lean_dec(v_a_155_);
lean_del_object(v___x_152_);
lean_dec(v_a_143_);
lean_dec(v_a_134_);
lean_dec(v_a_132_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
v_a_190_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_158_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_158_);
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
lean_del_object(v___x_152_);
lean_dec(v_a_143_);
lean_dec(v_a_134_);
lean_dec(v_a_132_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
v_a_198_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_154_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_154_);
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
}
else
{
lean_object* v___x_207_; lean_object* v___x_209_; 
lean_dec(v_a_146_);
lean_dec(v_a_143_);
lean_dec(v_a_134_);
lean_dec(v_a_132_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
v___x_207_ = lean_box(0);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_207_);
v___x_209_ = v___x_148_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v___x_207_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_a_143_);
lean_dec(v_a_134_);
lean_dec(v_a_132_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
v_a_212_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_145_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_145_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_a_134_);
lean_dec(v_a_132_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_atomExpr_117_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
lean_dec_ref(v_atom_114_);
v_a_220_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_142_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_142_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_134_);
lean_dec(v_a_132_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_atomExpr_117_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
lean_dec_ref(v_atom_114_);
v_a_228_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_140_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_140_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_132_);
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_atomExpr_117_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
lean_dec_ref(v_atom_114_);
v_a_236_ = lean_ctor_get(v___x_133_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_133_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_133_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_133_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v_rhsExpr_119_);
lean_dec_ref(v_lhsExpr_118_);
lean_dec_ref(v_atomExpr_117_);
lean_dec_ref(v_discrExpr_116_);
lean_dec_ref(v_lhs_115_);
lean_dec_ref(v_atom_114_);
lean_dec_ref(v_discr_113_);
v_a_244_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_131_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_131_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___boxed(lean_object* v_discr_252_, lean_object* v_atom_253_, lean_object* v_lhs_254_, lean_object* v_discrExpr_255_, lean_object* v_atomExpr_256_, lean_object* v_lhsExpr_257_, lean_object* v_rhsExpr_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_252_, v_atom_253_, v_lhs_254_, v_discrExpr_255_, v_atomExpr_256_, v_lhsExpr_257_, v_rhsExpr_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(lean_object* v_discr_267_, lean_object* v_atom_268_, lean_object* v_lhs_269_, lean_object* v_discrExpr_270_, lean_object* v_atomExpr_271_, lean_object* v_lhsExpr_272_, lean_object* v_rhsExpr_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_267_, v_atom_268_, v_lhs_269_, v_discrExpr_270_, v_atomExpr_271_, v_lhsExpr_272_, v_rhsExpr_273_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___boxed(lean_object* v_discr_284_, lean_object* v_atom_285_, lean_object* v_lhs_286_, lean_object* v_discrExpr_287_, lean_object* v_atomExpr_288_, lean_object* v_lhsExpr_289_, lean_object* v_rhsExpr_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(v_discr_284_, v_atom_285_, v_lhs_286_, v_discrExpr_287_, v_atomExpr_288_, v_lhsExpr_289_, v_rhsExpr_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
lean_dec(v_a_298_);
lean_dec_ref(v_a_297_);
lean_dec(v_a_296_);
lean_dec_ref(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_a_293_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(lean_object* v_expr_301_, lean_object* v_a_302_, lean_object* v_rhs_303_, lean_object* v_lemmaName_304_, lean_object* v___x_305_, lean_object* v_discrExpr_306_, lean_object* v_lhsExpr_307_, lean_object* v_rhsExpr_308_, lean_object* v___x_309_, lean_object* v___x_310_, lean_object* v___x_311_, lean_object* v___x_312_, lean_object* v___x_313_, lean_object* v___x_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_301_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_a_302_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_346_; 
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_346_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_346_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_346_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___y_332_; 
if (lean_obj_tag(v_a_327_) == 0)
{
lean_object* v___x_344_; 
lean_inc(v_a_325_);
v___x_344_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_325_);
v___y_332_ = v___x_344_;
goto v___jp_331_;
}
else
{
lean_object* v_val_345_; 
v_val_345_ = lean_ctor_get(v_a_327_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v_a_327_, 1);
v___y_332_ = v_val_345_;
goto v___jp_331_;
}
v___jp_331_:
{
lean_object* v_width_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_342_; 
v_width_333_ = lean_ctor_get(v_rhs_303_, 0);
lean_inc(v_width_333_);
lean_dec_ref(v_rhs_303_);
lean_inc(v___x_305_);
v___x_334_ = l_Lean_mkConst(v_lemmaName_304_, v___x_305_);
v___x_335_ = l_Lean_mkNatLit(v_width_333_);
v___x_336_ = l_Lean_mkApp4(v___x_334_, v___x_335_, v_discrExpr_306_, v_lhsExpr_307_, v_rhsExpr_308_);
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0));
v___x_338_ = l_Lean_Name_mkStr6(v___x_309_, v___x_310_, v___x_311_, v___x_312_, v___x_313_, v___x_337_);
v___x_339_ = l_Lean_mkConst(v___x_338_, v___x_305_);
v___x_340_ = l_Lean_mkApp4(v___x_339_, v___x_314_, v_a_325_, v___y_332_, v___x_336_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_340_);
v___x_342_ = v___x_329_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_340_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_a_325_);
lean_dec_ref(v___x_314_);
lean_dec_ref(v___x_313_);
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_311_);
lean_dec_ref(v___x_310_);
lean_dec_ref(v___x_309_);
lean_dec_ref(v_rhsExpr_308_);
lean_dec_ref(v_lhsExpr_307_);
lean_dec_ref(v_discrExpr_306_);
lean_dec(v___x_305_);
lean_dec(v_lemmaName_304_);
lean_dec_ref(v_rhs_303_);
v_a_347_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_326_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_326_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
else
{
lean_dec_ref(v___x_314_);
lean_dec_ref(v___x_313_);
lean_dec_ref(v___x_312_);
lean_dec_ref(v___x_311_);
lean_dec_ref(v___x_310_);
lean_dec_ref(v___x_309_);
lean_dec_ref(v_rhsExpr_308_);
lean_dec_ref(v_lhsExpr_307_);
lean_dec_ref(v_discrExpr_306_);
lean_dec(v___x_305_);
lean_dec(v_lemmaName_304_);
lean_dec_ref(v_rhs_303_);
lean_dec_ref(v_a_302_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_355_ = _args[0];
lean_object* v_a_356_ = _args[1];
lean_object* v_rhs_357_ = _args[2];
lean_object* v_lemmaName_358_ = _args[3];
lean_object* v___x_359_ = _args[4];
lean_object* v_discrExpr_360_ = _args[5];
lean_object* v_lhsExpr_361_ = _args[6];
lean_object* v_rhsExpr_362_ = _args[7];
lean_object* v___x_363_ = _args[8];
lean_object* v___x_364_ = _args[9];
lean_object* v___x_365_ = _args[10];
lean_object* v___x_366_ = _args[11];
lean_object* v___x_367_ = _args[12];
lean_object* v___x_368_ = _args[13];
lean_object* v___y_369_ = _args[14];
lean_object* v___y_370_ = _args[15];
lean_object* v___y_371_ = _args[16];
lean_object* v___y_372_ = _args[17];
lean_object* v___y_373_ = _args[18];
lean_object* v___y_374_ = _args[19];
lean_object* v___y_375_ = _args[20];
lean_object* v___y_376_ = _args[21];
lean_object* v___y_377_ = _args[22];
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(v_expr_355_, v_a_356_, v_rhs_357_, v_lemmaName_358_, v___x_359_, v_discrExpr_360_, v_lhsExpr_361_, v_rhsExpr_362_, v___x_363_, v___x_364_, v___x_365_, v___x_366_, v___x_367_, v___x_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(lean_object* v_discr_387_, lean_object* v_atom_388_, lean_object* v_rhs_389_, lean_object* v_discrExpr_390_, lean_object* v_atomExpr_391_, lean_object* v_lhsExpr_392_, lean_object* v_rhsExpr_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6));
v___x_402_ = lean_unsigned_to_nat(2u);
v___x_403_ = lean_mk_empty_array_with_capacity(v___x_402_);
lean_inc_ref(v_atomExpr_391_);
v___x_404_ = lean_array_push(v___x_403_, v_atomExpr_391_);
lean_inc_ref(v_rhsExpr_393_);
v___x_405_ = lean_array_push(v___x_404_, v_rhsExpr_393_);
v___x_406_ = l_Lean_Meta_mkAppM(v___x_401_, v___x_405_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_406_) == 0)
{
lean_object* v_a_407_; lean_object* v___x_408_; 
v_a_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v___x_406_, 1);
v___x_408_ = l_Lean_Meta_Sym_shareCommonInc(v_a_407_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; uint8_t v___x_410_; lean_object* v___x_411_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc_n(v_a_409_, 2);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = 0;
lean_inc_ref(v_rhsExpr_393_);
lean_inc_ref(v_rhs_389_);
v___x_411_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_atom_388_, v_rhs_389_, v_atomExpr_391_, v_rhsExpr_393_, v___x_410_, v_a_409_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_479_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_479_ == 0)
{
v___x_414_ = v___x_411_;
v_isShared_415_ = v_isSharedCheck_479_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_479_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
if (lean_obj_tag(v_a_412_) == 1)
{
lean_object* v_val_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_474_; 
lean_del_object(v___x_414_);
v_val_416_ = lean_ctor_get(v_a_412_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_a_412_);
if (v_isSharedCheck_474_ == 0)
{
v___x_418_ = v_a_412_;
v_isShared_419_ = v_isSharedCheck_474_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_val_416_);
lean_dec(v_a_412_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_474_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_416_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0));
v___x_423_ = lean_box(0);
v___x_424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9);
lean_inc(v_a_409_);
lean_inc_ref(v_discrExpr_390_);
v___x_425_ = l_Lean_mkAppB(v___x_424_, v_discrExpr_390_, v_a_409_);
lean_inc_ref(v___x_425_);
v___x_426_ = l_Lean_Meta_Sym_shareCommonInc(v___x_425_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; uint8_t v___x_428_; lean_object* v___x_429_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v___x_428_ = 3;
lean_inc_ref(v_discrExpr_390_);
v___x_429_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_discr_387_, v_a_421_, v_discrExpr_390_, v_a_409_, v___x_428_, v_a_427_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_449_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_449_ == 0)
{
v___x_432_ = v___x_429_;
v_isShared_433_ = v_isSharedCheck_449_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_449_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v_bvExpr_434_; lean_object* v_expr_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v_lemmaName_440_; lean_object* v___f_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v_bvExpr_434_ = lean_ctor_get(v_a_430_, 0);
lean_inc_ref(v_bvExpr_434_);
v_expr_435_ = lean_ctor_get(v_a_430_, 3);
lean_inc_ref_n(v_expr_435_, 2);
v___x_436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10));
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11));
v___x_438_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12));
v___x_439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13));
v_lemmaName_440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1));
v___f_441_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed), 23, 14);
lean_closure_set(v___f_441_, 0, v_expr_435_);
lean_closure_set(v___f_441_, 1, v_a_430_);
lean_closure_set(v___f_441_, 2, v_rhs_389_);
lean_closure_set(v___f_441_, 3, v_lemmaName_440_);
lean_closure_set(v___f_441_, 4, v___x_423_);
lean_closure_set(v___f_441_, 5, v_discrExpr_390_);
lean_closure_set(v___f_441_, 6, v_lhsExpr_392_);
lean_closure_set(v___f_441_, 7, v_rhsExpr_393_);
lean_closure_set(v___f_441_, 8, v___x_436_);
lean_closure_set(v___f_441_, 9, v___x_437_);
lean_closure_set(v___f_441_, 10, v___x_438_);
lean_closure_set(v___f_441_, 11, v___x_439_);
lean_closure_set(v___f_441_, 12, v___x_422_);
lean_closure_set(v___f_441_, 13, v___x_425_);
v___x_442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_442_, 0, v_bvExpr_434_);
lean_ctor_set(v___x_442_, 1, v___f_441_);
lean_ctor_set(v___x_442_, 2, v_expr_435_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 0, v___x_442_);
v___x_444_ = v___x_418_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_442_);
v___x_444_ = v_reuseFailAlloc_448_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_446_; 
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 0, v___x_444_);
v___x_446_ = v___x_432_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_457_; 
lean_dec_ref(v___x_425_);
lean_del_object(v___x_418_);
lean_dec_ref(v_rhsExpr_393_);
lean_dec_ref(v_lhsExpr_392_);
lean_dec_ref(v_discrExpr_390_);
lean_dec_ref(v_rhs_389_);
v_a_450_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_457_ == 0)
{
v___x_452_ = v___x_429_;
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_429_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_457_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_455_; 
if (v_isShared_453_ == 0)
{
v___x_455_ = v___x_452_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
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
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
lean_dec_ref(v___x_425_);
lean_dec(v_a_421_);
lean_del_object(v___x_418_);
lean_dec(v_a_409_);
lean_dec_ref(v_rhsExpr_393_);
lean_dec_ref(v_lhsExpr_392_);
lean_dec_ref(v_discrExpr_390_);
lean_dec_ref(v_rhs_389_);
lean_dec_ref(v_discr_387_);
v_a_458_ = lean_ctor_get(v___x_426_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_426_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_426_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
}
else
{
lean_object* v_a_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_473_; 
lean_del_object(v___x_418_);
lean_dec(v_a_409_);
lean_dec_ref(v_rhsExpr_393_);
lean_dec_ref(v_lhsExpr_392_);
lean_dec_ref(v_discrExpr_390_);
lean_dec_ref(v_rhs_389_);
lean_dec_ref(v_discr_387_);
v_a_466_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_473_ == 0)
{
v___x_468_ = v___x_420_;
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_a_466_);
lean_dec(v___x_420_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_473_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_471_; 
if (v_isShared_469_ == 0)
{
v___x_471_ = v___x_468_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_466_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
else
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec(v_a_412_);
lean_dec(v_a_409_);
lean_dec_ref(v_rhsExpr_393_);
lean_dec_ref(v_lhsExpr_392_);
lean_dec_ref(v_discrExpr_390_);
lean_dec_ref(v_rhs_389_);
lean_dec_ref(v_discr_387_);
v___x_475_ = lean_box(0);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_475_);
v___x_477_ = v___x_414_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_a_409_);
lean_dec_ref(v_rhsExpr_393_);
lean_dec_ref(v_lhsExpr_392_);
lean_dec_ref(v_discrExpr_390_);
lean_dec_ref(v_rhs_389_);
lean_dec_ref(v_discr_387_);
v_a_480_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_411_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_411_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec_ref(v_rhsExpr_393_);
lean_dec_ref(v_lhsExpr_392_);
lean_dec_ref(v_atomExpr_391_);
lean_dec_ref(v_discrExpr_390_);
lean_dec_ref(v_rhs_389_);
lean_dec_ref(v_atom_388_);
lean_dec_ref(v_discr_387_);
v_a_488_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_408_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_408_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_503_; 
lean_dec_ref(v_rhsExpr_393_);
lean_dec_ref(v_lhsExpr_392_);
lean_dec_ref(v_atomExpr_391_);
lean_dec_ref(v_discrExpr_390_);
lean_dec_ref(v_rhs_389_);
lean_dec_ref(v_atom_388_);
lean_dec_ref(v_discr_387_);
v_a_496_ = lean_ctor_get(v___x_406_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_503_ == 0)
{
v___x_498_ = v___x_406_;
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_406_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_503_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_501_; 
if (v_isShared_499_ == 0)
{
v___x_501_ = v___x_498_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_496_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___boxed(lean_object* v_discr_504_, lean_object* v_atom_505_, lean_object* v_rhs_506_, lean_object* v_discrExpr_507_, lean_object* v_atomExpr_508_, lean_object* v_lhsExpr_509_, lean_object* v_rhsExpr_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_504_, v_atom_505_, v_rhs_506_, v_discrExpr_507_, v_atomExpr_508_, v_lhsExpr_509_, v_rhsExpr_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(lean_object* v_discr_519_, lean_object* v_atom_520_, lean_object* v_rhs_521_, lean_object* v_discrExpr_522_, lean_object* v_atomExpr_523_, lean_object* v_lhsExpr_524_, lean_object* v_rhsExpr_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_519_, v_atom_520_, v_rhs_521_, v_discrExpr_522_, v_atomExpr_523_, v_lhsExpr_524_, v_rhsExpr_525_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___boxed(lean_object* v_discr_536_, lean_object* v_atom_537_, lean_object* v_rhs_538_, lean_object* v_discrExpr_539_, lean_object* v_atomExpr_540_, lean_object* v_lhsExpr_541_, lean_object* v_rhsExpr_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(v_discr_536_, v_atom_537_, v_rhs_538_, v_discrExpr_539_, v_atomExpr_540_, v_lhsExpr_541_, v_rhsExpr_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(lean_object* v_discr_553_, lean_object* v_atom_554_, lean_object* v_lhs_555_, lean_object* v_rhs_556_, lean_object* v_discrExpr_557_, lean_object* v_atomExpr_558_, lean_object* v_lhsExpr_559_, lean_object* v_rhsExpr_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; 
lean_inc_ref(v_rhsExpr_560_);
lean_inc_ref(v_lhsExpr_559_);
lean_inc_ref(v_atomExpr_558_);
lean_inc_ref(v_discrExpr_557_);
lean_inc_ref(v_atom_554_);
lean_inc_ref(v_discr_553_);
v___x_569_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_553_, v_atom_554_, v_lhs_555_, v_discrExpr_557_, v_atomExpr_558_, v_lhsExpr_559_, v_rhsExpr_560_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_569_) == 0)
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_600_; 
v_a_570_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_600_ == 0)
{
v___x_572_ = v___x_569_;
v_isShared_573_ = v_isSharedCheck_600_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_569_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_600_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
if (lean_obj_tag(v_a_570_) == 1)
{
lean_object* v_val_574_; lean_object* v___x_575_; 
lean_del_object(v___x_572_);
v_val_574_ = lean_ctor_get(v_a_570_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v_a_570_, 1);
v___x_575_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_val_574_, v_a_561_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; 
lean_dec_ref_known(v___x_575_, 1);
v___x_576_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_553_, v_atom_554_, v_rhs_556_, v_discrExpr_557_, v_atomExpr_558_, v_lhsExpr_559_, v_rhsExpr_560_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_587_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_587_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_587_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
if (lean_obj_tag(v_a_577_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_582_; 
lean_del_object(v___x_579_);
v_val_581_ = lean_ctor_get(v_a_577_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_a_577_, 1);
v___x_582_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_val_581_, v_a_561_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_585_; 
lean_dec(v_a_577_);
v___x_583_ = lean_box(0);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_583_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
v_a_588_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_576_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_576_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
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
lean_dec_ref(v_rhsExpr_560_);
lean_dec_ref(v_lhsExpr_559_);
lean_dec_ref(v_atomExpr_558_);
lean_dec_ref(v_discrExpr_557_);
lean_dec_ref(v_rhs_556_);
lean_dec_ref(v_atom_554_);
lean_dec_ref(v_discr_553_);
return v___x_575_;
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_598_; 
lean_dec(v_a_570_);
lean_dec_ref(v_rhsExpr_560_);
lean_dec_ref(v_lhsExpr_559_);
lean_dec_ref(v_atomExpr_558_);
lean_dec_ref(v_discrExpr_557_);
lean_dec_ref(v_rhs_556_);
lean_dec_ref(v_atom_554_);
lean_dec_ref(v_discr_553_);
v___x_596_ = lean_box(0);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 0, v___x_596_);
v___x_598_ = v___x_572_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
else
{
lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v_rhsExpr_560_);
lean_dec_ref(v_lhsExpr_559_);
lean_dec_ref(v_atomExpr_558_);
lean_dec_ref(v_discrExpr_557_);
lean_dec_ref(v_rhs_556_);
lean_dec_ref(v_atom_554_);
lean_dec_ref(v_discr_553_);
v_a_601_ = lean_ctor_get(v___x_569_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_569_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_569_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_569_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg___boxed(lean_object* v_discr_609_, lean_object* v_atom_610_, lean_object* v_lhs_611_, lean_object* v_rhs_612_, lean_object* v_discrExpr_613_, lean_object* v_atomExpr_614_, lean_object* v_lhsExpr_615_, lean_object* v_rhsExpr_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(v_discr_609_, v_atom_610_, v_lhs_611_, v_rhs_612_, v_discrExpr_613_, v_atomExpr_614_, v_lhsExpr_615_, v_rhsExpr_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas(lean_object* v_discr_626_, lean_object* v_atom_627_, lean_object* v_lhs_628_, lean_object* v_rhs_629_, lean_object* v_discrExpr_630_, lean_object* v_atomExpr_631_, lean_object* v_lhsExpr_632_, lean_object* v_rhsExpr_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(v_discr_626_, v_atom_627_, v_lhs_628_, v_rhs_629_, v_discrExpr_630_, v_atomExpr_631_, v_lhsExpr_632_, v_rhsExpr_633_, v_a_634_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___boxed(lean_object** _args){
lean_object* v_discr_645_ = _args[0];
lean_object* v_atom_646_ = _args[1];
lean_object* v_lhs_647_ = _args[2];
lean_object* v_rhs_648_ = _args[3];
lean_object* v_discrExpr_649_ = _args[4];
lean_object* v_atomExpr_650_ = _args[5];
lean_object* v_lhsExpr_651_ = _args[6];
lean_object* v_rhsExpr_652_ = _args[7];
lean_object* v_a_653_ = _args[8];
lean_object* v_a_654_ = _args[9];
lean_object* v_a_655_ = _args[10];
lean_object* v_a_656_ = _args[11];
lean_object* v_a_657_ = _args[12];
lean_object* v_a_658_ = _args[13];
lean_object* v_a_659_ = _args[14];
lean_object* v_a_660_ = _args[15];
lean_object* v_a_661_ = _args[16];
lean_object* v_a_662_ = _args[17];
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas(v_discr_645_, v_atom_646_, v_lhs_647_, v_rhs_648_, v_discrExpr_649_, v_atomExpr_650_, v_lhsExpr_651_, v_rhsExpr_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
return v_res_663_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas(builtin);
}
#ifdef __cplusplus
}
#endif

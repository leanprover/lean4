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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "lemma_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "cond_true"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(71, 253, 9, 241, 22, 101, 244, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(90, 191, 239, 225, 113, 224, 109, 182)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cond_false"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 177, 250, 0, 252, 101, 138, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___boxed(lean_object**);
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(lean_object* v_expr_2_, lean_object* v_a_3_, lean_object* v_lhs_4_, lean_object* v_lemmaName_5_, lean_object* v___x_6_, lean_object* v_discrExpr_7_, lean_object* v_lhsExpr_8_, lean_object* v_rhsExpr_9_, lean_object* v___x_10_, lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v___x_13_, lean_object* v___x_14_, lean_object* v___x_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_2_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v___x_30_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
lean_dec_ref_known(v___x_28_, 1);
v___x_30_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_a_3_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_50_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_50_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_50_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_50_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___y_36_; 
if (lean_obj_tag(v_a_31_) == 0)
{
lean_object* v___x_48_; 
lean_inc(v_a_29_);
v___x_48_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_29_);
v___y_36_ = v___x_48_;
goto v___jp_35_;
}
else
{
lean_object* v_val_49_; 
v_val_49_ = lean_ctor_get(v_a_31_, 0);
lean_inc(v_val_49_);
lean_dec_ref_known(v_a_31_, 1);
v___y_36_ = v_val_49_;
goto v___jp_35_;
}
v___jp_35_:
{
lean_object* v_width_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v_width_37_ = lean_ctor_get(v_lhs_4_, 0);
lean_inc(v_width_37_);
lean_dec_ref(v_lhs_4_);
lean_inc(v___x_6_);
v___x_38_ = l_Lean_mkConst(v_lemmaName_5_, v___x_6_);
v___x_39_ = l_Lean_mkNatLit(v_width_37_);
v___x_40_ = l_Lean_mkApp4(v___x_38_, v___x_39_, v_discrExpr_7_, v_lhsExpr_8_, v_rhsExpr_9_);
v___x_41_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0));
v___x_42_ = l_Lean_Name_mkStr6(v___x_10_, v___x_11_, v___x_12_, v___x_13_, v___x_14_, v___x_41_);
v___x_43_ = l_Lean_mkConst(v___x_42_, v___x_6_);
v___x_44_ = l_Lean_mkApp4(v___x_43_, v___x_15_, v_a_29_, v___y_36_, v___x_40_);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 0, v___x_44_);
v___x_46_ = v___x_33_;
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
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
lean_dec(v_a_29_);
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
v_a_51_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_30_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_30_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
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
return v___x_28_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_2_ = stack[0].m_obj;
lean_object* v_a_3_ = stack[1].m_obj;
lean_object* v_lhs_4_ = stack[2].m_obj;
lean_object* v_lemmaName_5_ = stack[3].m_obj;
lean_object* v___x_6_ = stack[4].m_obj;
lean_object* v_discrExpr_7_ = stack[5].m_obj;
lean_object* v_lhsExpr_8_ = stack[6].m_obj;
lean_object* v_rhsExpr_9_ = stack[7].m_obj;
lean_object* v___x_10_ = stack[8].m_obj;
lean_object* v___x_11_ = stack[9].m_obj;
lean_object* v___x_12_ = stack[10].m_obj;
lean_object* v___x_13_ = stack[11].m_obj;
lean_object* v___x_14_ = stack[12].m_obj;
lean_object* v___x_15_ = stack[13].m_obj;
lean_object* v___y_16_ = stack[14].m_obj;
lean_object* v___y_17_ = stack[15].m_obj;
lean_object* v___y_18_ = stack[16].m_obj;
lean_object* v___y_19_ = stack[17].m_obj;
lean_object* v___y_20_ = stack[18].m_obj;
lean_object* v___y_21_ = stack[19].m_obj;
lean_object* v___y_22_ = stack[20].m_obj;
lean_object* v___y_23_ = stack[21].m_obj;
lean_object* v___y_24_ = stack[22].m_obj;
lean_object* v___y_25_ = stack[23].m_obj;
lean_object* v___y_26_ = stack[24].m_obj;
lean_object* v_res_59_;
v_res_59_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(v_expr_2_, v_a_3_, v_lhs_4_, v_lemmaName_5_, v___x_6_, v_discrExpr_7_, v_lhsExpr_8_, v_rhsExpr_9_, v___x_10_, v___x_11_, v___x_12_, v___x_13_, v___x_14_, v___x_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_60_ = _args[0];
lean_object* v_a_61_ = _args[1];
lean_object* v_lhs_62_ = _args[2];
lean_object* v_lemmaName_63_ = _args[3];
lean_object* v___x_64_ = _args[4];
lean_object* v_discrExpr_65_ = _args[5];
lean_object* v_lhsExpr_66_ = _args[6];
lean_object* v_rhsExpr_67_ = _args[7];
lean_object* v___x_68_ = _args[8];
lean_object* v___x_69_ = _args[9];
lean_object* v___x_70_ = _args[10];
lean_object* v___x_71_ = _args[11];
lean_object* v___x_72_ = _args[12];
lean_object* v___x_73_ = _args[13];
lean_object* v___y_74_ = _args[14];
lean_object* v___y_75_ = _args[15];
lean_object* v___y_76_ = _args[16];
lean_object* v___y_77_ = _args[17];
lean_object* v___y_78_ = _args[18];
lean_object* v___y_79_ = _args[19];
lean_object* v___y_80_ = _args[20];
lean_object* v___y_81_ = _args[21];
lean_object* v___y_82_ = _args[22];
lean_object* v___y_83_ = _args[23];
lean_object* v___y_84_ = _args[24];
lean_object* v___y_85_ = _args[25];
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0(v_expr_60_, v_a_61_, v_lhs_62_, v_lemmaName_63_, v___x_64_, v_discrExpr_65_, v_lhsExpr_66_, v_rhsExpr_67_, v___x_68_, v___x_69_, v___x_70_, v___x_71_, v___x_72_, v___x_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_86_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_box(0);
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__9));
v___x_107_ = l_Lean_mkConst(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(0);
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__15));
v___x_119_ = l_Lean_mkConst(v___x_118_, v___x_117_);
return v___x_119_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(lean_object* v_discr_120_, lean_object* v_atom_121_, lean_object* v_lhs_122_, lean_object* v_discrExpr_123_, lean_object* v_atomExpr_124_, lean_object* v_lhsExpr_125_, lean_object* v_rhsExpr_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v_lemmaName_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0));
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1));
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2));
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3));
v_lemmaName_138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__6));
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7));
v___x_140_ = lean_box(0);
v___x_141_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__10);
lean_inc_ref(v_discrExpr_123_);
v___x_142_ = l_Lean_Expr_app___override(v___x_141_, v_discrExpr_123_);
v___x_143_ = l_Lean_Meta_Sym_shareCommonInc(v___x_142_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_145_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc_n(v_a_144_, 2);
lean_dec_ref_known(v___x_143_, 1);
lean_inc_ref(v_discrExpr_123_);
v___x_145_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_discr_120_, v_discrExpr_123_, v_a_144_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_object* v_a_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_a_146_ = lean_ctor_get(v___x_145_, 0);
lean_inc(v_a_146_);
lean_dec_ref_known(v___x_145_, 1);
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13));
v___x_148_ = lean_unsigned_to_nat(2u);
v___x_149_ = lean_mk_empty_array_with_capacity(v___x_148_);
lean_inc_ref(v_atomExpr_124_);
v___x_150_ = lean_array_push(v___x_149_, v_atomExpr_124_);
lean_inc_ref(v_lhsExpr_125_);
v___x_151_ = lean_array_push(v___x_150_, v_lhsExpr_125_);
v___x_152_ = l_Lean_Meta_mkAppM(v___x_147_, v___x_151_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_154_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v___x_152_, 1);
v___x_154_ = l_Lean_Meta_Sym_shareCommonInc(v_a_153_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; uint8_t v___x_156_; lean_object* v___x_157_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc_n(v_a_155_, 2);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = 0;
lean_inc_ref(v_lhsExpr_125_);
lean_inc_ref(v_lhs_122_);
v___x_157_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_atom_121_, v_lhs_122_, v_atomExpr_124_, v_lhsExpr_125_, v___x_156_, v_a_155_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_218_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_218_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_218_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_218_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
if (lean_obj_tag(v_a_158_) == 1)
{
lean_object* v_val_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_213_; 
lean_del_object(v___x_160_);
v_val_162_ = lean_ctor_get(v_a_158_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_a_158_);
if (v_isSharedCheck_213_ == 0)
{
v___x_164_ = v_a_158_;
v_isShared_165_ = v_isSharedCheck_213_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_val_162_);
lean_dec(v_a_158_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_213_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_162_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16);
lean_inc(v_a_155_);
lean_inc(v_a_144_);
v___x_169_ = l_Lean_mkAppB(v___x_168_, v_a_144_, v_a_155_);
lean_inc_ref(v___x_169_);
v___x_170_ = l_Lean_Meta_Sym_shareCommonInc(v___x_169_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; uint8_t v___x_172_; lean_object* v___x_173_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
lean_inc(v_a_171_);
lean_dec_ref_known(v___x_170_, 1);
v___x_172_ = 3;
v___x_173_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_a_146_, v_a_167_, v_a_144_, v_a_155_, v___x_172_, v_a_171_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_173_) == 0)
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_188_; 
v_a_174_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_188_ == 0)
{
v___x_176_ = v___x_173_;
v_isShared_177_ = v_isSharedCheck_188_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_173_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_188_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_bvExpr_178_; lean_object* v_expr_179_; lean_object* v___f_180_; lean_object* v___x_181_; lean_object* v___x_183_; 
v_bvExpr_178_ = lean_ctor_get(v_a_174_, 0);
lean_inc_ref(v_bvExpr_178_);
v_expr_179_ = lean_ctor_get(v_a_174_, 3);
lean_inc_ref_n(v_expr_179_, 2);
v___f_180_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___boxed), 26, 14);
lean_closure_set(v___f_180_, 0, v_expr_179_);
lean_closure_set(v___f_180_, 1, v_a_174_);
lean_closure_set(v___f_180_, 2, v_lhs_122_);
lean_closure_set(v___f_180_, 3, v_lemmaName_138_);
lean_closure_set(v___f_180_, 4, v___x_140_);
lean_closure_set(v___f_180_, 5, v_discrExpr_123_);
lean_closure_set(v___f_180_, 6, v_lhsExpr_125_);
lean_closure_set(v___f_180_, 7, v_rhsExpr_126_);
lean_closure_set(v___f_180_, 8, v___x_134_);
lean_closure_set(v___f_180_, 9, v___x_135_);
lean_closure_set(v___f_180_, 10, v___x_136_);
lean_closure_set(v___f_180_, 11, v___x_137_);
lean_closure_set(v___f_180_, 12, v___x_139_);
lean_closure_set(v___f_180_, 13, v___x_169_);
v___x_181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_181_, 0, v_bvExpr_178_);
lean_ctor_set(v___x_181_, 1, v___f_180_);
lean_ctor_set(v___x_181_, 2, v_expr_179_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_181_);
v___x_183_ = v___x_164_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_187_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
lean_object* v___x_185_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_183_);
v___x_185_ = v___x_176_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec_ref(v___x_169_);
lean_del_object(v___x_164_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
v_a_189_ = lean_ctor_get(v___x_173_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_173_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_173_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v___x_169_);
lean_dec(v_a_167_);
lean_del_object(v___x_164_);
lean_dec(v_a_155_);
lean_dec(v_a_146_);
lean_dec(v_a_144_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
v_a_197_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_170_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_170_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_del_object(v___x_164_);
lean_dec(v_a_155_);
lean_dec(v_a_146_);
lean_dec(v_a_144_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
v_a_205_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_166_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_166_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
else
{
lean_object* v___x_214_; lean_object* v___x_216_; 
lean_dec(v_a_158_);
lean_dec(v_a_155_);
lean_dec(v_a_146_);
lean_dec(v_a_144_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
v___x_214_ = lean_box(0);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_214_);
v___x_216_ = v___x_160_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
lean_dec(v_a_155_);
lean_dec(v_a_146_);
lean_dec(v_a_144_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
v_a_219_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_157_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_157_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
lean_dec(v_a_146_);
lean_dec(v_a_144_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_atomExpr_124_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
lean_dec_ref(v_atom_121_);
v_a_227_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_154_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_154_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_a_146_);
lean_dec(v_a_144_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_atomExpr_124_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
lean_dec_ref(v_atom_121_);
v_a_235_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_152_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_152_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
else
{
lean_object* v_a_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_250_; 
lean_dec(v_a_144_);
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_atomExpr_124_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
lean_dec_ref(v_atom_121_);
v_a_243_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_250_ == 0)
{
v___x_245_ = v___x_145_;
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_a_243_);
lean_dec(v___x_145_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_250_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_a_243_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
}
}
else
{
lean_object* v_a_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v_rhsExpr_126_);
lean_dec_ref(v_lhsExpr_125_);
lean_dec_ref(v_atomExpr_124_);
lean_dec_ref(v_discrExpr_123_);
lean_dec_ref(v_lhs_122_);
lean_dec_ref(v_atom_121_);
lean_dec_ref(v_discr_120_);
v_a_251_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_258_ == 0)
{
v___x_253_ = v___x_143_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_a_251_);
lean_dec(v___x_143_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_a_251_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_120_ = stack[0].m_obj;
lean_object* v_atom_121_ = stack[1].m_obj;
lean_object* v_lhs_122_ = stack[2].m_obj;
lean_object* v_discrExpr_123_ = stack[3].m_obj;
lean_object* v_atomExpr_124_ = stack[4].m_obj;
lean_object* v_lhsExpr_125_ = stack[5].m_obj;
lean_object* v_rhsExpr_126_ = stack[6].m_obj;
lean_object* v_a_127_ = stack[7].m_obj;
lean_object* v_a_128_ = stack[8].m_obj;
lean_object* v_a_129_ = stack[9].m_obj;
lean_object* v_a_130_ = stack[10].m_obj;
lean_object* v_a_131_ = stack[11].m_obj;
lean_object* v_a_132_ = stack[12].m_obj;
lean_object* v_res_259_;
v_res_259_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_120_, v_atom_121_, v_lhs_122_, v_discrExpr_123_, v_atomExpr_124_, v_lhsExpr_125_, v_rhsExpr_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
stack->m_obj
 = v_res_259_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___boxed(lean_object* v_discr_260_, lean_object* v_atom_261_, lean_object* v_lhs_262_, lean_object* v_discrExpr_263_, lean_object* v_atomExpr_264_, lean_object* v_lhsExpr_265_, lean_object* v_rhsExpr_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_260_, v_atom_261_, v_lhs_262_, v_discrExpr_263_, v_atomExpr_264_, v_lhsExpr_265_, v_rhsExpr_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_274_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(lean_object* v_discr_275_, lean_object* v_atom_276_, lean_object* v_lhs_277_, lean_object* v_discrExpr_278_, lean_object* v_atomExpr_279_, lean_object* v_lhsExpr_280_, lean_object* v_rhsExpr_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_275_, v_atom_276_, v_lhs_277_, v_discrExpr_278_, v_atomExpr_279_, v_lhsExpr_280_, v_rhsExpr_281_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
return v___x_294_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_275_ = stack[0].m_obj;
lean_object* v_atom_276_ = stack[1].m_obj;
lean_object* v_lhs_277_ = stack[2].m_obj;
lean_object* v_discrExpr_278_ = stack[3].m_obj;
lean_object* v_atomExpr_279_ = stack[4].m_obj;
lean_object* v_lhsExpr_280_ = stack[5].m_obj;
lean_object* v_rhsExpr_281_ = stack[6].m_obj;
lean_object* v_a_282_ = stack[7].m_obj;
lean_object* v_a_283_ = stack[8].m_obj;
lean_object* v_a_284_ = stack[9].m_obj;
lean_object* v_a_285_ = stack[10].m_obj;
lean_object* v_a_286_ = stack[11].m_obj;
lean_object* v_a_287_ = stack[12].m_obj;
lean_object* v_a_288_ = stack[13].m_obj;
lean_object* v_a_289_ = stack[14].m_obj;
lean_object* v_a_290_ = stack[15].m_obj;
lean_object* v_a_291_ = stack[16].m_obj;
lean_object* v_a_292_ = stack[17].m_obj;
lean_object* v_res_295_;
v_res_295_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(v_discr_275_, v_atom_276_, v_lhs_277_, v_discrExpr_278_, v_atomExpr_279_, v_lhsExpr_280_, v_rhsExpr_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___boxed(lean_object** _args){
lean_object* v_discr_296_ = _args[0];
lean_object* v_atom_297_ = _args[1];
lean_object* v_lhs_298_ = _args[2];
lean_object* v_discrExpr_299_ = _args[3];
lean_object* v_atomExpr_300_ = _args[4];
lean_object* v_lhsExpr_301_ = _args[5];
lean_object* v_rhsExpr_302_ = _args[6];
lean_object* v_a_303_ = _args[7];
lean_object* v_a_304_ = _args[8];
lean_object* v_a_305_ = _args[9];
lean_object* v_a_306_ = _args[10];
lean_object* v_a_307_ = _args[11];
lean_object* v_a_308_ = _args[12];
lean_object* v_a_309_ = _args[13];
lean_object* v_a_310_ = _args[14];
lean_object* v_a_311_ = _args[15];
lean_object* v_a_312_ = _args[16];
lean_object* v_a_313_ = _args[17];
lean_object* v_a_314_ = _args[18];
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma(v_discr_296_, v_atom_297_, v_lhs_298_, v_discrExpr_299_, v_atomExpr_300_, v_lhsExpr_301_, v_rhsExpr_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
lean_dec(v_a_307_);
lean_dec_ref(v_a_306_);
lean_dec(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
return v_res_315_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(lean_object* v_expr_316_, lean_object* v_a_317_, lean_object* v_rhs_318_, lean_object* v_lemmaName_319_, lean_object* v___x_320_, lean_object* v_discrExpr_321_, lean_object* v_lhsExpr_322_, lean_object* v_rhsExpr_323_, lean_object* v___x_324_, lean_object* v___x_325_, lean_object* v___x_326_, lean_object* v___x_327_, lean_object* v___x_328_, lean_object* v___x_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_316_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_a_317_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_364_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_364_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_364_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_364_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___y_350_; 
if (lean_obj_tag(v_a_345_) == 0)
{
lean_object* v___x_362_; 
lean_inc(v_a_343_);
v___x_362_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_343_);
v___y_350_ = v___x_362_;
goto v___jp_349_;
}
else
{
lean_object* v_val_363_; 
v_val_363_ = lean_ctor_get(v_a_345_, 0);
lean_inc(v_val_363_);
lean_dec_ref_known(v_a_345_, 1);
v___y_350_ = v_val_363_;
goto v___jp_349_;
}
v___jp_349_:
{
lean_object* v_width_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v_width_351_ = lean_ctor_get(v_rhs_318_, 0);
lean_inc(v_width_351_);
lean_dec_ref(v_rhs_318_);
lean_inc(v___x_320_);
v___x_352_ = l_Lean_mkConst(v_lemmaName_319_, v___x_320_);
v___x_353_ = l_Lean_mkNatLit(v_width_351_);
v___x_354_ = l_Lean_mkApp4(v___x_352_, v___x_353_, v_discrExpr_321_, v_lhsExpr_322_, v_rhsExpr_323_);
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___lam__0___closed__0));
v___x_356_ = l_Lean_Name_mkStr6(v___x_324_, v___x_325_, v___x_326_, v___x_327_, v___x_328_, v___x_355_);
v___x_357_ = l_Lean_mkConst(v___x_356_, v___x_320_);
v___x_358_ = l_Lean_mkApp4(v___x_357_, v___x_329_, v_a_343_, v___y_350_, v___x_354_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v___x_358_);
v___x_360_ = v___x_347_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec(v_a_343_);
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_324_);
lean_dec_ref(v_rhsExpr_323_);
lean_dec_ref(v_lhsExpr_322_);
lean_dec_ref(v_discrExpr_321_);
lean_dec(v___x_320_);
lean_dec(v_lemmaName_319_);
lean_dec_ref(v_rhs_318_);
v_a_365_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_344_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_344_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_dec_ref(v___x_329_);
lean_dec_ref(v___x_328_);
lean_dec_ref(v___x_327_);
lean_dec_ref(v___x_326_);
lean_dec_ref(v___x_325_);
lean_dec_ref(v___x_324_);
lean_dec_ref(v_rhsExpr_323_);
lean_dec_ref(v_lhsExpr_322_);
lean_dec_ref(v_discrExpr_321_);
lean_dec(v___x_320_);
lean_dec(v_lemmaName_319_);
lean_dec_ref(v_rhs_318_);
lean_dec_ref(v_a_317_);
return v___x_342_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_316_ = stack[0].m_obj;
lean_object* v_a_317_ = stack[1].m_obj;
lean_object* v_rhs_318_ = stack[2].m_obj;
lean_object* v_lemmaName_319_ = stack[3].m_obj;
lean_object* v___x_320_ = stack[4].m_obj;
lean_object* v_discrExpr_321_ = stack[5].m_obj;
lean_object* v_lhsExpr_322_ = stack[6].m_obj;
lean_object* v_rhsExpr_323_ = stack[7].m_obj;
lean_object* v___x_324_ = stack[8].m_obj;
lean_object* v___x_325_ = stack[9].m_obj;
lean_object* v___x_326_ = stack[10].m_obj;
lean_object* v___x_327_ = stack[11].m_obj;
lean_object* v___x_328_ = stack[12].m_obj;
lean_object* v___x_329_ = stack[13].m_obj;
lean_object* v___y_330_ = stack[14].m_obj;
lean_object* v___y_331_ = stack[15].m_obj;
lean_object* v___y_332_ = stack[16].m_obj;
lean_object* v___y_333_ = stack[17].m_obj;
lean_object* v___y_334_ = stack[18].m_obj;
lean_object* v___y_335_ = stack[19].m_obj;
lean_object* v___y_336_ = stack[20].m_obj;
lean_object* v___y_337_ = stack[21].m_obj;
lean_object* v___y_338_ = stack[22].m_obj;
lean_object* v___y_339_ = stack[23].m_obj;
lean_object* v___y_340_ = stack[24].m_obj;
lean_object* v_res_373_;
v_res_373_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(v_expr_316_, v_a_317_, v_rhs_318_, v_lemmaName_319_, v___x_320_, v_discrExpr_321_, v_lhsExpr_322_, v_rhsExpr_323_, v___x_324_, v___x_325_, v___x_326_, v___x_327_, v___x_328_, v___x_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
stack->m_obj
 = v_res_373_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_374_ = _args[0];
lean_object* v_a_375_ = _args[1];
lean_object* v_rhs_376_ = _args[2];
lean_object* v_lemmaName_377_ = _args[3];
lean_object* v___x_378_ = _args[4];
lean_object* v_discrExpr_379_ = _args[5];
lean_object* v_lhsExpr_380_ = _args[6];
lean_object* v_rhsExpr_381_ = _args[7];
lean_object* v___x_382_ = _args[8];
lean_object* v___x_383_ = _args[9];
lean_object* v___x_384_ = _args[10];
lean_object* v___x_385_ = _args[11];
lean_object* v___x_386_ = _args[12];
lean_object* v___x_387_ = _args[13];
lean_object* v___y_388_ = _args[14];
lean_object* v___y_389_ = _args[15];
lean_object* v___y_390_ = _args[16];
lean_object* v___y_391_ = _args[17];
lean_object* v___y_392_ = _args[18];
lean_object* v___y_393_ = _args[19];
lean_object* v___y_394_ = _args[20];
lean_object* v___y_395_ = _args[21];
lean_object* v___y_396_ = _args[22];
lean_object* v___y_397_ = _args[23];
lean_object* v___y_398_ = _args[24];
lean_object* v___y_399_ = _args[25];
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0(v_expr_374_, v_a_375_, v_rhs_376_, v_lemmaName_377_, v___x_378_, v_discrExpr_379_, v_lhsExpr_380_, v_rhsExpr_381_, v___x_382_, v___x_383_, v___x_384_, v___x_385_, v___x_386_, v___x_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_400_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(lean_object* v_discr_409_, lean_object* v_atom_410_, lean_object* v_rhs_411_, lean_object* v_discrExpr_412_, lean_object* v_atomExpr_413_, lean_object* v_lhsExpr_414_, lean_object* v_rhsExpr_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v_lemmaName_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__0));
v___x_424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__1));
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__2));
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__3));
v_lemmaName_427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___closed__1));
v___x_428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__13));
v___x_429_ = lean_unsigned_to_nat(2u);
v___x_430_ = lean_mk_empty_array_with_capacity(v___x_429_);
lean_inc_ref(v_atomExpr_413_);
v___x_431_ = lean_array_push(v___x_430_, v_atomExpr_413_);
lean_inc_ref(v_rhsExpr_415_);
v___x_432_ = lean_array_push(v___x_431_, v_rhsExpr_415_);
v___x_433_ = l_Lean_Meta_mkAppM(v___x_428_, v___x_432_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_435_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = l_Lean_Meta_Sym_shareCommonInc(v_a_434_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; uint8_t v___x_437_; lean_object* v___x_438_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
lean_inc_n(v_a_436_, 2);
lean_dec_ref_known(v___x_435_, 1);
v___x_437_ = 0;
lean_inc_ref(v_rhsExpr_415_);
lean_inc_ref(v_rhs_411_);
v___x_438_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_atom_410_, v_rhs_411_, v_atomExpr_413_, v_rhsExpr_415_, v___x_437_, v_a_436_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_438_) == 0)
{
lean_object* v_a_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_501_; 
v_a_439_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_501_ == 0)
{
v___x_441_ = v___x_438_;
v_isShared_442_ = v_isSharedCheck_501_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_a_439_);
lean_dec(v___x_438_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_501_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
if (lean_obj_tag(v_a_439_) == 1)
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_496_; 
lean_del_object(v___x_441_);
v_val_443_ = lean_ctor_get(v_a_439_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v_a_439_);
if (v_isSharedCheck_496_ == 0)
{
v___x_445_ = v_a_439_;
v_isShared_446_ = v_isSharedCheck_496_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v_a_439_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_496_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_443_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__7));
v___x_450_ = lean_box(0);
v___x_451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg___closed__16);
lean_inc(v_a_436_);
lean_inc_ref(v_discrExpr_412_);
v___x_452_ = l_Lean_mkAppB(v___x_451_, v_discrExpr_412_, v_a_436_);
lean_inc_ref(v___x_452_);
v___x_453_ = l_Lean_Meta_Sym_shareCommonInc(v___x_452_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
lean_inc(v_a_454_);
lean_dec_ref_known(v___x_453_, 1);
v___x_455_ = 3;
lean_inc_ref(v_discrExpr_412_);
v___x_456_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_discr_409_, v_a_448_, v_discrExpr_412_, v_a_436_, v___x_455_, v_a_454_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_471_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_471_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_471_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_471_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_bvExpr_461_; lean_object* v_expr_462_; lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v_bvExpr_461_ = lean_ctor_get(v_a_457_, 0);
lean_inc_ref(v_bvExpr_461_);
v_expr_462_ = lean_ctor_get(v_a_457_, 3);
lean_inc_ref_n(v_expr_462_, 2);
v___f_463_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___lam__0___boxed), 26, 14);
lean_closure_set(v___f_463_, 0, v_expr_462_);
lean_closure_set(v___f_463_, 1, v_a_457_);
lean_closure_set(v___f_463_, 2, v_rhs_411_);
lean_closure_set(v___f_463_, 3, v_lemmaName_427_);
lean_closure_set(v___f_463_, 4, v___x_450_);
lean_closure_set(v___f_463_, 5, v_discrExpr_412_);
lean_closure_set(v___f_463_, 6, v_lhsExpr_414_);
lean_closure_set(v___f_463_, 7, v_rhsExpr_415_);
lean_closure_set(v___f_463_, 8, v___x_423_);
lean_closure_set(v___f_463_, 9, v___x_424_);
lean_closure_set(v___f_463_, 10, v___x_425_);
lean_closure_set(v___f_463_, 11, v___x_426_);
lean_closure_set(v___f_463_, 12, v___x_449_);
lean_closure_set(v___f_463_, 13, v___x_452_);
v___x_464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_464_, 0, v_bvExpr_461_);
lean_ctor_set(v___x_464_, 1, v___f_463_);
lean_ctor_set(v___x_464_, 2, v_expr_462_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_464_);
v___x_466_ = v___x_445_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_466_);
v___x_468_ = v___x_459_;
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
lean_object* v_a_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_479_; 
lean_dec_ref(v___x_452_);
lean_del_object(v___x_445_);
lean_dec_ref(v_rhsExpr_415_);
lean_dec_ref(v_lhsExpr_414_);
lean_dec_ref(v_discrExpr_412_);
lean_dec_ref(v_rhs_411_);
v_a_472_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_479_ == 0)
{
v___x_474_ = v___x_456_;
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_a_472_);
lean_dec(v___x_456_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_479_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_477_; 
if (v_isShared_475_ == 0)
{
v___x_477_ = v___x_474_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_a_472_);
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
lean_dec_ref(v___x_452_);
lean_dec(v_a_448_);
lean_del_object(v___x_445_);
lean_dec(v_a_436_);
lean_dec_ref(v_rhsExpr_415_);
lean_dec_ref(v_lhsExpr_414_);
lean_dec_ref(v_discrExpr_412_);
lean_dec_ref(v_rhs_411_);
lean_dec_ref(v_discr_409_);
v_a_480_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_453_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_453_);
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
lean_del_object(v___x_445_);
lean_dec(v_a_436_);
lean_dec_ref(v_rhsExpr_415_);
lean_dec_ref(v_lhsExpr_414_);
lean_dec_ref(v_discrExpr_412_);
lean_dec_ref(v_rhs_411_);
lean_dec_ref(v_discr_409_);
v_a_488_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_447_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_447_);
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
}
else
{
lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_a_439_);
lean_dec(v_a_436_);
lean_dec_ref(v_rhsExpr_415_);
lean_dec_ref(v_lhsExpr_414_);
lean_dec_ref(v_discrExpr_412_);
lean_dec_ref(v_rhs_411_);
lean_dec_ref(v_discr_409_);
v___x_497_ = lean_box(0);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 0, v___x_497_);
v___x_499_ = v___x_441_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
lean_dec(v_a_436_);
lean_dec_ref(v_rhsExpr_415_);
lean_dec_ref(v_lhsExpr_414_);
lean_dec_ref(v_discrExpr_412_);
lean_dec_ref(v_rhs_411_);
lean_dec_ref(v_discr_409_);
v_a_502_ = lean_ctor_get(v___x_438_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_438_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_438_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_rhsExpr_415_);
lean_dec_ref(v_lhsExpr_414_);
lean_dec_ref(v_atomExpr_413_);
lean_dec_ref(v_discrExpr_412_);
lean_dec_ref(v_rhs_411_);
lean_dec_ref(v_atom_410_);
lean_dec_ref(v_discr_409_);
v_a_510_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_435_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_435_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v_rhsExpr_415_);
lean_dec_ref(v_lhsExpr_414_);
lean_dec_ref(v_atomExpr_413_);
lean_dec_ref(v_discrExpr_412_);
lean_dec_ref(v_rhs_411_);
lean_dec_ref(v_atom_410_);
lean_dec_ref(v_discr_409_);
v_a_518_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_433_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_433_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_409_ = stack[0].m_obj;
lean_object* v_atom_410_ = stack[1].m_obj;
lean_object* v_rhs_411_ = stack[2].m_obj;
lean_object* v_discrExpr_412_ = stack[3].m_obj;
lean_object* v_atomExpr_413_ = stack[4].m_obj;
lean_object* v_lhsExpr_414_ = stack[5].m_obj;
lean_object* v_rhsExpr_415_ = stack[6].m_obj;
lean_object* v_a_416_ = stack[7].m_obj;
lean_object* v_a_417_ = stack[8].m_obj;
lean_object* v_a_418_ = stack[9].m_obj;
lean_object* v_a_419_ = stack[10].m_obj;
lean_object* v_a_420_ = stack[11].m_obj;
lean_object* v_a_421_ = stack[12].m_obj;
lean_object* v_res_526_;
v_res_526_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_409_, v_atom_410_, v_rhs_411_, v_discrExpr_412_, v_atomExpr_413_, v_lhsExpr_414_, v_rhsExpr_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
stack->m_obj
 = v_res_526_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg___boxed(lean_object* v_discr_527_, lean_object* v_atom_528_, lean_object* v_rhs_529_, lean_object* v_discrExpr_530_, lean_object* v_atomExpr_531_, lean_object* v_lhsExpr_532_, lean_object* v_rhsExpr_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_527_, v_atom_528_, v_rhs_529_, v_discrExpr_530_, v_atomExpr_531_, v_lhsExpr_532_, v_rhsExpr_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
return v_res_541_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(lean_object* v_discr_542_, lean_object* v_atom_543_, lean_object* v_rhs_544_, lean_object* v_discrExpr_545_, lean_object* v_atomExpr_546_, lean_object* v_lhsExpr_547_, lean_object* v_rhsExpr_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_542_, v_atom_543_, v_rhs_544_, v_discrExpr_545_, v_atomExpr_546_, v_lhsExpr_547_, v_rhsExpr_548_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_561_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_542_ = stack[0].m_obj;
lean_object* v_atom_543_ = stack[1].m_obj;
lean_object* v_rhs_544_ = stack[2].m_obj;
lean_object* v_discrExpr_545_ = stack[3].m_obj;
lean_object* v_atomExpr_546_ = stack[4].m_obj;
lean_object* v_lhsExpr_547_ = stack[5].m_obj;
lean_object* v_rhsExpr_548_ = stack[6].m_obj;
lean_object* v_a_549_ = stack[7].m_obj;
lean_object* v_a_550_ = stack[8].m_obj;
lean_object* v_a_551_ = stack[9].m_obj;
lean_object* v_a_552_ = stack[10].m_obj;
lean_object* v_a_553_ = stack[11].m_obj;
lean_object* v_a_554_ = stack[12].m_obj;
lean_object* v_a_555_ = stack[13].m_obj;
lean_object* v_a_556_ = stack[14].m_obj;
lean_object* v_a_557_ = stack[15].m_obj;
lean_object* v_a_558_ = stack[16].m_obj;
lean_object* v_a_559_ = stack[17].m_obj;
lean_object* v_res_562_;
v_res_562_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(v_discr_542_, v_atom_543_, v_rhs_544_, v_discrExpr_545_, v_atomExpr_546_, v_lhsExpr_547_, v_rhsExpr_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___boxed(lean_object** _args){
lean_object* v_discr_563_ = _args[0];
lean_object* v_atom_564_ = _args[1];
lean_object* v_rhs_565_ = _args[2];
lean_object* v_discrExpr_566_ = _args[3];
lean_object* v_atomExpr_567_ = _args[4];
lean_object* v_lhsExpr_568_ = _args[5];
lean_object* v_rhsExpr_569_ = _args[6];
lean_object* v_a_570_ = _args[7];
lean_object* v_a_571_ = _args[8];
lean_object* v_a_572_ = _args[9];
lean_object* v_a_573_ = _args[10];
lean_object* v_a_574_ = _args[11];
lean_object* v_a_575_ = _args[12];
lean_object* v_a_576_ = _args[13];
lean_object* v_a_577_ = _args[14];
lean_object* v_a_578_ = _args[15];
lean_object* v_a_579_ = _args[16];
lean_object* v_a_580_ = _args[17];
lean_object* v_a_581_ = _args[18];
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma(v_discr_563_, v_atom_564_, v_rhs_565_, v_discrExpr_566_, v_atomExpr_567_, v_lhsExpr_568_, v_rhsExpr_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec(v_a_571_);
lean_dec_ref(v_a_570_);
return v_res_582_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(lean_object* v_discr_583_, lean_object* v_atom_584_, lean_object* v_lhs_585_, lean_object* v_rhs_586_, lean_object* v_discrExpr_587_, lean_object* v_atomExpr_588_, lean_object* v_lhsExpr_589_, lean_object* v_rhsExpr_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; 
lean_inc_ref(v_rhsExpr_590_);
lean_inc_ref(v_lhsExpr_589_);
lean_inc_ref(v_atomExpr_588_);
lean_inc_ref(v_discrExpr_587_);
lean_inc_ref(v_atom_584_);
lean_inc_ref(v_discr_583_);
v___x_599_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondTrueLemma___redArg(v_discr_583_, v_atom_584_, v_lhs_585_, v_discrExpr_587_, v_atomExpr_588_, v_lhsExpr_589_, v_rhsExpr_590_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_630_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_630_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_630_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_630_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
if (lean_obj_tag(v_a_600_) == 1)
{
lean_object* v_val_604_; lean_object* v___x_605_; 
lean_del_object(v___x_602_);
v_val_604_ = lean_ctor_get(v_a_600_, 0);
lean_inc(v_val_604_);
lean_dec_ref_known(v_a_600_, 1);
v___x_605_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_val_604_, v_a_591_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_606_; 
lean_dec_ref_known(v___x_605_, 1);
v___x_606_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedLemmas_0__Lean_Meta_Tactic_BVDecide_addCondLemmas_mkCondFalseLemma___redArg(v_discr_583_, v_atom_584_, v_rhs_586_, v_discrExpr_587_, v_atomExpr_588_, v_lhsExpr_589_, v_rhsExpr_590_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_617_; 
v_a_607_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_617_ == 0)
{
v___x_609_ = v___x_606_;
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_606_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_617_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
if (lean_obj_tag(v_a_607_) == 1)
{
lean_object* v_val_611_; lean_object* v___x_612_; 
lean_del_object(v___x_609_);
v_val_611_ = lean_ctor_get(v_a_607_, 0);
lean_inc(v_val_611_);
lean_dec_ref_known(v_a_607_, 1);
v___x_612_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_val_611_, v_a_591_);
return v___x_612_;
}
else
{
lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v_a_607_);
v___x_613_ = lean_box(0);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_613_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
else
{
lean_object* v_a_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_625_; 
v_a_618_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_625_ == 0)
{
v___x_620_ = v___x_606_;
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_a_618_);
lean_dec(v___x_606_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_625_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
if (v_isShared_621_ == 0)
{
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
else
{
lean_dec_ref(v_rhsExpr_590_);
lean_dec_ref(v_lhsExpr_589_);
lean_dec_ref(v_atomExpr_588_);
lean_dec_ref(v_discrExpr_587_);
lean_dec_ref(v_rhs_586_);
lean_dec_ref(v_atom_584_);
lean_dec_ref(v_discr_583_);
return v___x_605_;
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_628_; 
lean_dec(v_a_600_);
lean_dec_ref(v_rhsExpr_590_);
lean_dec_ref(v_lhsExpr_589_);
lean_dec_ref(v_atomExpr_588_);
lean_dec_ref(v_discrExpr_587_);
lean_dec_ref(v_rhs_586_);
lean_dec_ref(v_atom_584_);
lean_dec_ref(v_discr_583_);
v___x_626_ = lean_box(0);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_626_);
v___x_628_ = v___x_602_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec_ref(v_rhsExpr_590_);
lean_dec_ref(v_lhsExpr_589_);
lean_dec_ref(v_atomExpr_588_);
lean_dec_ref(v_discrExpr_587_);
lean_dec_ref(v_rhs_586_);
lean_dec_ref(v_atom_584_);
lean_dec_ref(v_discr_583_);
v_a_631_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_599_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_599_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_583_ = stack[0].m_obj;
lean_object* v_atom_584_ = stack[1].m_obj;
lean_object* v_lhs_585_ = stack[2].m_obj;
lean_object* v_rhs_586_ = stack[3].m_obj;
lean_object* v_discrExpr_587_ = stack[4].m_obj;
lean_object* v_atomExpr_588_ = stack[5].m_obj;
lean_object* v_lhsExpr_589_ = stack[6].m_obj;
lean_object* v_rhsExpr_590_ = stack[7].m_obj;
lean_object* v_a_591_ = stack[8].m_obj;
lean_object* v_a_592_ = stack[9].m_obj;
lean_object* v_a_593_ = stack[10].m_obj;
lean_object* v_a_594_ = stack[11].m_obj;
lean_object* v_a_595_ = stack[12].m_obj;
lean_object* v_a_596_ = stack[13].m_obj;
lean_object* v_a_597_ = stack[14].m_obj;
lean_object* v_res_639_;
v_res_639_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(v_discr_583_, v_atom_584_, v_lhs_585_, v_rhs_586_, v_discrExpr_587_, v_atomExpr_588_, v_lhsExpr_589_, v_rhsExpr_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_);
stack->m_obj
 = v_res_639_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg___boxed(lean_object* v_discr_640_, lean_object* v_atom_641_, lean_object* v_lhs_642_, lean_object* v_rhs_643_, lean_object* v_discrExpr_644_, lean_object* v_atomExpr_645_, lean_object* v_lhsExpr_646_, lean_object* v_rhsExpr_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(v_discr_640_, v_atom_641_, v_lhs_642_, v_rhs_643_, v_discrExpr_644_, v_atomExpr_645_, v_lhsExpr_646_, v_rhsExpr_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
lean_dec(v_a_648_);
return v_res_656_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas(lean_object* v_discr_657_, lean_object* v_atom_658_, lean_object* v_lhs_659_, lean_object* v_rhs_660_, lean_object* v_discrExpr_661_, lean_object* v_atomExpr_662_, lean_object* v_lhsExpr_663_, lean_object* v_rhsExpr_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas___redArg(v_discr_657_, v_atom_658_, v_lhs_659_, v_rhs_660_, v_discrExpr_661_, v_atomExpr_662_, v_lhsExpr_663_, v_rhsExpr_664_, v_a_665_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
return v___x_678_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_addCondLemmas_0interp(lean_interpreter_value* stack)
{
lean_object* v_discr_657_ = stack[0].m_obj;
lean_object* v_atom_658_ = stack[1].m_obj;
lean_object* v_lhs_659_ = stack[2].m_obj;
lean_object* v_rhs_660_ = stack[3].m_obj;
lean_object* v_discrExpr_661_ = stack[4].m_obj;
lean_object* v_atomExpr_662_ = stack[5].m_obj;
lean_object* v_lhsExpr_663_ = stack[6].m_obj;
lean_object* v_rhsExpr_664_ = stack[7].m_obj;
lean_object* v_a_665_ = stack[8].m_obj;
lean_object* v_a_666_ = stack[9].m_obj;
lean_object* v_a_667_ = stack[10].m_obj;
lean_object* v_a_668_ = stack[11].m_obj;
lean_object* v_a_669_ = stack[12].m_obj;
lean_object* v_a_670_ = stack[13].m_obj;
lean_object* v_a_671_ = stack[14].m_obj;
lean_object* v_a_672_ = stack[15].m_obj;
lean_object* v_a_673_ = stack[16].m_obj;
lean_object* v_a_674_ = stack[17].m_obj;
lean_object* v_a_675_ = stack[18].m_obj;
lean_object* v_a_676_ = stack[19].m_obj;
lean_object* v_res_679_;
v_res_679_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas(v_discr_657_, v_atom_658_, v_lhs_659_, v_rhs_660_, v_discrExpr_661_, v_atomExpr_662_, v_lhsExpr_663_, v_rhsExpr_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
stack->m_obj
 = v_res_679_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_addCondLemmas___boxed(lean_object** _args){
lean_object* v_discr_680_ = _args[0];
lean_object* v_atom_681_ = _args[1];
lean_object* v_lhs_682_ = _args[2];
lean_object* v_rhs_683_ = _args[3];
lean_object* v_discrExpr_684_ = _args[4];
lean_object* v_atomExpr_685_ = _args[5];
lean_object* v_lhsExpr_686_ = _args[6];
lean_object* v_rhsExpr_687_ = _args[7];
lean_object* v_a_688_ = _args[8];
lean_object* v_a_689_ = _args[9];
lean_object* v_a_690_ = _args[10];
lean_object* v_a_691_ = _args[11];
lean_object* v_a_692_ = _args[12];
lean_object* v_a_693_ = _args[13];
lean_object* v_a_694_ = _args[14];
lean_object* v_a_695_ = _args[15];
lean_object* v_a_696_ = _args[16];
lean_object* v_a_697_ = _args[17];
lean_object* v_a_698_ = _args[18];
lean_object* v_a_699_ = _args[19];
lean_object* v_a_700_ = _args[20];
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_Tactic_BVDecide_addCondLemmas(v_discr_680_, v_atom_681_, v_lhs_682_, v_rhs_683_, v_discrExpr_684_, v_atomExpr_685_, v_lhsExpr_686_, v_rhsExpr_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec(v_a_688_);
return v_res_701_;
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

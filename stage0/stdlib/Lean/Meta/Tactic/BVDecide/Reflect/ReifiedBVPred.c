// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Basic import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr import Lean.Meta.Sym.InferType
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
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "beq_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__5_value),LEAN_SCALAR_PTR_LITERAL(11, 253, 163, 204, 112, 81, 92, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ult_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__4_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__7_value),LEAN_SCALAR_PTR_LITERAL(147, 192, 184, 158, 23, 221, 204, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(36, 213, 64, 10, 224, 53, 8, 130)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "BVBinPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(110, 124, 151, 202, 173, 235, 72, 127)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ult"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(64, 63, 119, 185, 54, 210, 178, 92)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "getLsbD_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(233, 227, 220, 143, 67, 138, 133, 64)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(uint8_t v_pred_22_){
_start:
{
if (v_pred_22_ == 0)
{
lean_object* v___x_23_; 
v___x_23_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__6));
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
v___x_24_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__8));
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___boxed(lean_object* v_pred_25_){
_start:
{
uint8_t v_pred_boxed_26_; lean_object* v_res_27_; 
v_pred_boxed_26_ = lean_unbox(v_pred_25_);
v_res_27_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(v_pred_boxed_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(lean_object* v___x_28_, lean_object* v_fst_29_, lean_object* v_fproof_30_, lean_object* v_snd_31_, lean_object* v_sproof_32_){
_start:
{
if (lean_obj_tag(v_fproof_30_) == 0)
{
lean_dec_ref(v_snd_31_);
if (lean_obj_tag(v_sproof_32_) == 0)
{
lean_object* v___x_33_; 
lean_dec_ref(v_fst_29_);
lean_dec(v___x_28_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
else
{
lean_object* v_val_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_43_; 
v_val_34_ = lean_ctor_get(v_sproof_32_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v_sproof_32_);
if (v_isSharedCheck_43_ == 0)
{
v___x_36_ = v_sproof_32_;
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_val_34_);
lean_dec(v_sproof_32_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_43_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_41_; 
v___x_38_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_28_, v_fst_29_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v_val_34_);
if (v_isShared_37_ == 0)
{
lean_ctor_set(v___x_36_, 0, v___x_39_);
v___x_41_ = v___x_36_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v___x_39_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
else
{
lean_dec_ref(v_fst_29_);
if (lean_obj_tag(v_sproof_32_) == 0)
{
lean_object* v_val_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_53_; 
v_val_44_ = lean_ctor_get(v_fproof_30_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v_fproof_30_);
if (v_isSharedCheck_53_ == 0)
{
v___x_46_ = v_fproof_30_;
v_isShared_47_ = v_isSharedCheck_53_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_val_44_);
lean_dec(v_fproof_30_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_53_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_48_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_28_, v_snd_31_);
v___x_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_49_, 0, v_val_44_);
lean_ctor_set(v___x_49_, 1, v___x_48_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_49_);
v___x_51_ = v___x_46_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v_val_54_; lean_object* v_val_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_63_; 
lean_dec_ref(v_snd_31_);
lean_dec(v___x_28_);
v_val_54_ = lean_ctor_get(v_fproof_30_, 0);
lean_inc(v_val_54_);
lean_dec_ref_known(v_fproof_30_, 1);
v_val_55_ = lean_ctor_get(v_sproof_32_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_sproof_32_);
if (v_isSharedCheck_63_ == 0)
{
v___x_57_ = v_sproof_32_;
v_isShared_58_ = v_isSharedCheck_63_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_val_55_);
lean_dec(v_sproof_32_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_63_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v___x_61_; 
v___x_59_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_59_, 0, v_val_54_);
lean_ctor_set(v___x_59_, 1, v_val_55_);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_59_);
v___x_61_ = v___x_57_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v___x_59_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(lean_object* v_width_64_, lean_object* v_expr_65_, lean_object* v_width_66_, lean_object* v_expr_67_, lean_object* v_lhs_68_, lean_object* v_rhs_69_, lean_object* v_congrThm_70_, lean_object* v___x_71_, lean_object* v___x_72_, lean_object* v_lhsExpr_73_, lean_object* v_rhsExpr_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; 
lean_inc(v_width_64_);
v___x_87_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_64_, v_expr_65_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_66_, v_expr_67_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v___x_91_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_89_, 1);
v___x_91_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_lhs_68_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_93_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
lean_dec_ref_known(v___x_91_, 1);
v___x_93_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_rhs_69_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_118_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_118_ == 0)
{
v___x_96_ = v___x_93_;
v_isShared_97_ = v_isSharedCheck_118_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_a_94_);
lean_dec(v___x_93_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_118_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; 
lean_inc(v_a_90_);
lean_inc(v_a_88_);
v___x_98_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(v_width_64_, v_a_88_, v_a_92_, v_a_90_, v_a_94_);
if (lean_obj_tag(v___x_98_) == 1)
{
lean_object* v_val_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_113_; 
v_val_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_113_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_113_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_val_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_113_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_fst_103_; lean_object* v_snd_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v_fst_103_ = lean_ctor_get(v_val_99_, 0);
lean_inc(v_fst_103_);
v_snd_104_ = lean_ctor_get(v_val_99_, 1);
lean_inc(v_snd_104_);
lean_dec(v_val_99_);
v___x_105_ = l_Lean_mkConst(v_congrThm_70_, v___x_71_);
v___x_106_ = l_Lean_mkApp7(v___x_105_, v___x_72_, v_lhsExpr_73_, v_rhsExpr_74_, v_a_88_, v_a_90_, v_fst_103_, v_snd_104_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v___x_106_);
v___x_108_ = v___x_101_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_112_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_110_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_108_);
v___x_110_ = v___x_96_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_object* v___x_114_; lean_object* v___x_116_; 
lean_dec(v___x_98_);
lean_dec(v_a_90_);
lean_dec(v_a_88_);
lean_dec_ref(v_rhsExpr_74_);
lean_dec_ref(v_lhsExpr_73_);
lean_dec_ref(v___x_72_);
lean_dec(v___x_71_);
lean_dec(v_congrThm_70_);
v___x_114_ = lean_box(0);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_114_);
v___x_116_ = v___x_96_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
else
{
lean_dec(v_a_92_);
lean_dec(v_a_90_);
lean_dec(v_a_88_);
lean_dec_ref(v_rhsExpr_74_);
lean_dec_ref(v_lhsExpr_73_);
lean_dec_ref(v___x_72_);
lean_dec(v___x_71_);
lean_dec(v_congrThm_70_);
lean_dec(v_width_64_);
return v___x_93_;
}
}
else
{
lean_dec(v_a_90_);
lean_dec(v_a_88_);
lean_dec_ref(v_rhsExpr_74_);
lean_dec_ref(v_lhsExpr_73_);
lean_dec_ref(v___x_72_);
lean_dec(v___x_71_);
lean_dec(v_congrThm_70_);
lean_dec_ref(v_rhs_69_);
lean_dec(v_width_64_);
return v___x_91_;
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
lean_dec(v_a_88_);
lean_dec_ref(v_rhsExpr_74_);
lean_dec_ref(v_lhsExpr_73_);
lean_dec_ref(v___x_72_);
lean_dec(v___x_71_);
lean_dec(v_congrThm_70_);
lean_dec_ref(v_rhs_69_);
lean_dec_ref(v_lhs_68_);
lean_dec(v_width_64_);
v_a_119_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_89_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_89_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_dec_ref(v_rhsExpr_74_);
lean_dec_ref(v_lhsExpr_73_);
lean_dec_ref(v___x_72_);
lean_dec(v___x_71_);
lean_dec(v_congrThm_70_);
lean_dec_ref(v_rhs_69_);
lean_dec_ref(v_lhs_68_);
lean_dec_ref(v_expr_67_);
lean_dec(v_width_66_);
lean_dec(v_width_64_);
v_a_127_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_87_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_87_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_width_135_ = _args[0];
lean_object* v_expr_136_ = _args[1];
lean_object* v_width_137_ = _args[2];
lean_object* v_expr_138_ = _args[3];
lean_object* v_lhs_139_ = _args[4];
lean_object* v_rhs_140_ = _args[5];
lean_object* v_congrThm_141_ = _args[6];
lean_object* v___x_142_ = _args[7];
lean_object* v___x_143_ = _args[8];
lean_object* v_lhsExpr_144_ = _args[9];
lean_object* v_rhsExpr_145_ = _args[10];
lean_object* v___y_146_ = _args[11];
lean_object* v___y_147_ = _args[12];
lean_object* v___y_148_ = _args[13];
lean_object* v___y_149_ = _args[14];
lean_object* v___y_150_ = _args[15];
lean_object* v___y_151_ = _args[16];
lean_object* v___y_152_ = _args[17];
lean_object* v___y_153_ = _args[18];
lean_object* v___y_154_ = _args[19];
lean_object* v___y_155_ = _args[20];
lean_object* v___y_156_ = _args[21];
lean_object* v___y_157_ = _args[22];
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(v_width_135_, v_expr_136_, v_width_137_, v_expr_138_, v_lhs_139_, v_rhs_140_, v_congrThm_141_, v___x_142_, v___x_143_, v_lhsExpr_144_, v_rhsExpr_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_158_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(0);
v___x_168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2));
v___x_169_ = l_Lean_mkConst(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(0);
v___x_179_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6));
v___x_180_ = l_Lean_mkConst(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__10(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = lean_box(0);
v___x_189_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9));
v___x_190_ = l_Lean_mkConst(v___x_189_, v___x_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(lean_object* v_lhs_191_, lean_object* v_rhs_192_, lean_object* v_lhsExpr_193_, lean_object* v_rhsExpr_194_, uint8_t v_pred_195_, lean_object* v_origExpr_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_width_204_; lean_object* v_bvExpr_205_; lean_object* v_expr_206_; lean_object* v_width_207_; lean_object* v_bvExpr_208_; lean_object* v_expr_209_; uint8_t v___x_210_; 
v_width_204_ = lean_ctor_get(v_lhs_191_, 0);
lean_inc(v_width_204_);
v_bvExpr_205_ = lean_ctor_get(v_lhs_191_, 1);
v_expr_206_ = lean_ctor_get(v_lhs_191_, 4);
lean_inc_ref(v_expr_206_);
v_width_207_ = lean_ctor_get(v_rhs_192_, 0);
lean_inc(v_width_207_);
v_bvExpr_208_ = lean_ctor_get(v_rhs_192_, 1);
v_expr_209_ = lean_ctor_get(v_rhs_192_, 4);
lean_inc_ref(v_expr_209_);
v___x_210_ = lean_nat_dec_eq(v_width_204_, v_width_207_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v_expr_209_);
lean_dec(v_width_207_);
lean_dec_ref(v_expr_206_);
lean_dec(v_width_204_);
lean_dec_ref(v_origExpr_196_);
lean_dec_ref(v_rhsExpr_194_);
lean_dec_ref(v_lhsExpr_193_);
lean_dec_ref(v_rhs_192_);
lean_dec_ref(v_lhs_191_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
return v___x_212_;
}
else
{
lean_object* v_congrThm_213_; lean_object* v_bvExpr_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___y_220_; 
v_congrThm_213_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(v_pred_195_);
lean_inc_ref(v_bvExpr_208_);
lean_inc_ref(v_bvExpr_205_);
lean_inc_n(v_width_204_, 2);
v_bvExpr_214_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_bvExpr_214_, 0, v_width_204_);
lean_ctor_set(v_bvExpr_214_, 1, v_bvExpr_205_);
lean_ctor_set(v_bvExpr_214_, 2, v_bvExpr_208_);
lean_ctor_set_uint8(v_bvExpr_214_, sizeof(void*)*3, v_pred_195_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3);
v___x_217_ = l_Lean_mkNatLit(v_width_204_);
lean_inc_ref(v___x_217_);
lean_inc_ref(v_expr_209_);
lean_inc_ref(v_expr_206_);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed), 23, 11);
lean_closure_set(v___f_218_, 0, v_width_204_);
lean_closure_set(v___f_218_, 1, v_expr_206_);
lean_closure_set(v___f_218_, 2, v_width_207_);
lean_closure_set(v___f_218_, 3, v_expr_209_);
lean_closure_set(v___f_218_, 4, v_lhs_191_);
lean_closure_set(v___f_218_, 5, v_rhs_192_);
lean_closure_set(v___f_218_, 6, v_congrThm_213_);
lean_closure_set(v___f_218_, 7, v___x_215_);
lean_closure_set(v___f_218_, 8, v___x_217_);
lean_closure_set(v___f_218_, 9, v_lhsExpr_193_);
lean_closure_set(v___f_218_, 10, v_rhsExpr_194_);
if (v_pred_195_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7);
v___y_220_ = v___x_241_;
goto v___jp_219_;
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__10, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__10);
v___y_220_ = v___x_242_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_inc_ref(v___y_220_);
v___x_221_ = l_Lean_mkApp4(v___x_216_, v___x_217_, v_expr_206_, v___y_220_, v_expr_209_);
v___x_222_ = l_Lean_Meta_Sym_shareCommonInc(v___x_221_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_232_; 
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_232_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_232_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_232_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_227_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_227_, 0, v_bvExpr_214_);
lean_ctor_set(v___x_227_, 1, v_origExpr_196_);
lean_ctor_set(v___x_227_, 2, v___f_218_);
lean_ctor_set(v___x_227_, 3, v_a_223_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_228_);
v___x_230_ = v___x_225_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_240_; 
lean_dec_ref(v___f_218_);
lean_dec_ref_known(v_bvExpr_214_, 3);
lean_dec_ref(v_origExpr_196_);
v_a_233_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_240_ == 0)
{
v___x_235_ = v___x_222_;
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_222_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_240_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_a_233_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___boxed(lean_object* v_lhs_243_, lean_object* v_rhs_244_, lean_object* v_lhsExpr_245_, lean_object* v_rhsExpr_246_, lean_object* v_pred_247_, lean_object* v_origExpr_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
uint8_t v_pred_boxed_256_; lean_object* v_res_257_; 
v_pred_boxed_256_ = lean_unbox(v_pred_247_);
v_res_257_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_lhs_243_, v_rhs_244_, v_lhsExpr_245_, v_rhsExpr_246_, v_pred_boxed_256_, v_origExpr_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_a_253_);
lean_dec(v_a_252_);
lean_dec_ref(v_a_251_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(lean_object* v_lhs_258_, lean_object* v_rhs_259_, lean_object* v_lhsExpr_260_, lean_object* v_rhsExpr_261_, uint8_t v_pred_262_, lean_object* v_origExpr_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_lhs_258_, v_rhs_259_, v_lhsExpr_260_, v_rhsExpr_261_, v_pred_262_, v_origExpr_263_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___boxed(lean_object** _args){
lean_object* v_lhs_277_ = _args[0];
lean_object* v_rhs_278_ = _args[1];
lean_object* v_lhsExpr_279_ = _args[2];
lean_object* v_rhsExpr_280_ = _args[3];
lean_object* v_pred_281_ = _args[4];
lean_object* v_origExpr_282_ = _args[5];
lean_object* v_a_283_ = _args[6];
lean_object* v_a_284_ = _args[7];
lean_object* v_a_285_ = _args[8];
lean_object* v_a_286_ = _args[9];
lean_object* v_a_287_ = _args[10];
lean_object* v_a_288_ = _args[11];
lean_object* v_a_289_ = _args[12];
lean_object* v_a_290_ = _args[13];
lean_object* v_a_291_ = _args[14];
lean_object* v_a_292_ = _args[15];
lean_object* v_a_293_ = _args[16];
lean_object* v_a_294_ = _args[17];
_start:
{
uint8_t v_pred_boxed_295_; lean_object* v_res_296_; 
v_pred_boxed_295_ = lean_unbox(v_pred_281_);
v_res_296_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(v_lhs_277_, v_rhs_278_, v_lhsExpr_279_, v_rhsExpr_280_, v_pred_boxed_295_, v_origExpr_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(lean_object* v_sub_298_, lean_object* v_width_299_, lean_object* v_expr_300_, lean_object* v___x_301_, lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v_idxExpr_305_, lean_object* v___x_306_, lean_object* v_subExpr_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_sub_298_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_360_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_360_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_360_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_360_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
if (lean_obj_tag(v_a_321_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_355_; 
lean_del_object(v___x_323_);
v_val_325_ = lean_ctor_get(v_a_321_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_a_321_);
if (v_isSharedCheck_355_ == 0)
{
v___x_327_ = v_a_321_;
v_isShared_328_ = v_isSharedCheck_355_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_a_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_355_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_299_, v_expr_300_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_346_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_346_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_346_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_346_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3));
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__4));
v___x_336_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0));
v___x_337_ = l_Lean_Name_mkStr6(v___x_301_, v___x_302_, v___x_303_, v___x_334_, v___x_335_, v___x_336_);
v___x_338_ = l_Lean_mkConst(v___x_337_, v___x_304_);
v___x_339_ = l_Lean_mkApp5(v___x_338_, v_idxExpr_305_, v___x_306_, v_subExpr_307_, v_a_330_, v_val_325_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_339_);
v___x_341_ = v___x_327_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_345_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_343_; 
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_341_);
v___x_343_ = v___x_332_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v___x_341_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_del_object(v___x_327_);
lean_dec(v_val_325_);
lean_dec_ref(v_subExpr_307_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_idxExpr_305_);
lean_dec(v___x_304_);
lean_dec_ref(v___x_303_);
lean_dec_ref(v___x_302_);
lean_dec_ref(v___x_301_);
v_a_347_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_329_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_329_);
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
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v_a_321_);
lean_dec_ref(v_subExpr_307_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_idxExpr_305_);
lean_dec(v___x_304_);
lean_dec_ref(v___x_303_);
lean_dec_ref(v___x_302_);
lean_dec_ref(v___x_301_);
lean_dec_ref(v_expr_300_);
lean_dec(v_width_299_);
v___x_356_ = lean_box(0);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_356_);
v___x_358_ = v___x_323_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_dec_ref(v_subExpr_307_);
lean_dec_ref(v___x_306_);
lean_dec_ref(v_idxExpr_305_);
lean_dec(v___x_304_);
lean_dec_ref(v___x_303_);
lean_dec_ref(v___x_302_);
lean_dec_ref(v___x_301_);
lean_dec_ref(v_expr_300_);
lean_dec(v_width_299_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_sub_361_ = _args[0];
lean_object* v_width_362_ = _args[1];
lean_object* v_expr_363_ = _args[2];
lean_object* v___x_364_ = _args[3];
lean_object* v___x_365_ = _args[4];
lean_object* v___x_366_ = _args[5];
lean_object* v___x_367_ = _args[6];
lean_object* v_idxExpr_368_ = _args[7];
lean_object* v___x_369_ = _args[8];
lean_object* v_subExpr_370_ = _args[9];
lean_object* v___y_371_ = _args[10];
lean_object* v___y_372_ = _args[11];
lean_object* v___y_373_ = _args[12];
lean_object* v___y_374_ = _args[13];
lean_object* v___y_375_ = _args[14];
lean_object* v___y_376_ = _args[15];
lean_object* v___y_377_ = _args[16];
lean_object* v___y_378_ = _args[17];
lean_object* v___y_379_ = _args[18];
lean_object* v___y_380_ = _args[19];
lean_object* v___y_381_ = _args[20];
lean_object* v___y_382_ = _args[21];
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(v_sub_361_, v_width_362_, v_expr_363_, v___x_364_, v___x_365_, v___x_366_, v___x_367_, v_idxExpr_368_, v___x_369_, v_subExpr_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_383_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__2(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_box(0);
v___x_392_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__1));
v___x_393_ = l_Lean_mkConst(v___x_392_, v___x_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(lean_object* v_sub_394_, lean_object* v_subExpr_395_, lean_object* v_idx_396_, lean_object* v_origExpr_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_width_405_; lean_object* v_bvExpr_406_; lean_object* v_expr_407_; lean_object* v_bvExpr_408_; lean_object* v_idxExpr_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___f_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_width_405_ = lean_ctor_get(v_sub_394_, 0);
lean_inc_n(v_width_405_, 3);
v_bvExpr_406_ = lean_ctor_get(v_sub_394_, 1);
v_expr_407_ = lean_ctor_get(v_sub_394_, 4);
lean_inc_ref_n(v_expr_407_, 2);
lean_inc(v_idx_396_);
lean_inc_ref(v_bvExpr_406_);
v_bvExpr_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_bvExpr_408_, 0, v_width_405_);
lean_ctor_set(v_bvExpr_408_, 1, v_bvExpr_406_);
lean_ctor_set(v_bvExpr_408_, 2, v_idx_396_);
v_idxExpr_409_ = l_Lean_mkNatLit(v_idx_396_);
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0));
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1));
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2));
v___x_413_ = lean_box(0);
v___x_414_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___closed__2);
v___x_415_ = l_Lean_mkNatLit(v_width_405_);
lean_inc_ref(v___x_415_);
lean_inc_ref(v_idxExpr_409_);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed), 22, 10);
lean_closure_set(v___f_416_, 0, v_sub_394_);
lean_closure_set(v___f_416_, 1, v_width_405_);
lean_closure_set(v___f_416_, 2, v_expr_407_);
lean_closure_set(v___f_416_, 3, v___x_410_);
lean_closure_set(v___f_416_, 4, v___x_411_);
lean_closure_set(v___f_416_, 5, v___x_412_);
lean_closure_set(v___f_416_, 6, v___x_413_);
lean_closure_set(v___f_416_, 7, v_idxExpr_409_);
lean_closure_set(v___f_416_, 8, v___x_415_);
lean_closure_set(v___f_416_, 9, v_subExpr_395_);
v___x_417_ = l_Lean_mkApp3(v___x_414_, v___x_415_, v_expr_407_, v_idxExpr_409_);
v___x_418_ = l_Lean_Meta_Sym_shareCommonInc(v___x_417_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_427_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_427_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_427_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_423_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_423_, 0, v_bvExpr_408_);
lean_ctor_set(v___x_423_, 1, v_origExpr_397_);
lean_ctor_set(v___x_423_, 2, v___f_416_);
lean_ctor_set(v___x_423_, 3, v_a_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_423_);
v___x_425_ = v___x_421_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v___f_416_);
lean_dec_ref_known(v_bvExpr_408_, 3);
lean_dec_ref(v_origExpr_397_);
v_a_428_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_418_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_418_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___boxed(lean_object* v_sub_436_, lean_object* v_subExpr_437_, lean_object* v_idx_438_, lean_object* v_origExpr_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(v_sub_436_, v_subExpr_437_, v_idx_438_, v_origExpr_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_);
lean_dec(v_a_445_);
lean_dec_ref(v_a_444_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(lean_object* v_sub_448_, lean_object* v_subExpr_449_, lean_object* v_idx_450_, lean_object* v_origExpr_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(v_sub_448_, v_subExpr_449_, v_idx_450_, v_origExpr_451_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___boxed(lean_object* v_sub_465_, lean_object* v_subExpr_466_, lean_object* v_idx_467_, lean_object* v_origExpr_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(v_sub_465_, v_subExpr_466_, v_idx_467_, v_origExpr_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
lean_dec(v_a_473_);
lean_dec_ref(v_a_472_);
lean_dec(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
return v_res_481_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofBool_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 35, 113, 77, 117, 41, 40, 246)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__10_value),LEAN_SCALAR_PTR_LITERAL(233, 227, 220, 143, 67, 138, 133, 64)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "beq_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 253, 163, 204, 112, 81, 92, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ult_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 160, 70, 158, 0, 14, 153, 5)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(147, 192, 184, 158, 23, 221, 204, 187)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__9_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(36, 213, 64, 10, 224, 53, 8, 130)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "BVBinPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(110, 124, 151, 202, 173, 235, 72, 127)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ult"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(64, 63, 119, 185, 54, 210, 178, 92)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "getLsbD_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(lean_object* v_width_3_, lean_object* v_expr_4_, lean_object* v_a_5_, lean_object* v___x_6_, lean_object* v___x_7_, lean_object* v___x_8_, lean_object* v___x_9_, lean_object* v___x_10_, lean_object* v_origExpr_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v___x_21_; 
lean_inc(v_width_3_);
v___x_21_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_3_, v_expr_4_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v_a_22_; lean_object* v___x_23_; 
v_a_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_a_22_);
lean_dec_ref_known(v___x_21_, 1);
v___x_23_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_a_5_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_41_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_41_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_41_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_41_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___y_29_; 
if (lean_obj_tag(v_a_24_) == 0)
{
lean_object* v___x_39_; 
lean_inc(v_a_22_);
v___x_39_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v_width_3_, v_a_22_);
v___y_29_ = v___x_39_;
goto v___jp_28_;
}
else
{
lean_object* v_val_40_; 
lean_dec(v_width_3_);
v_val_40_ = lean_ctor_get(v_a_24_, 0);
lean_inc(v_val_40_);
lean_dec_ref_known(v_a_24_, 1);
v___y_29_ = v_val_40_;
goto v___jp_28_;
}
v___jp_28_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_30_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0));
v___x_31_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__1));
v___x_32_ = l_Lean_Name_mkStr6(v___x_6_, v___x_7_, v___x_8_, v___x_30_, v___x_9_, v___x_31_);
v___x_33_ = l_Lean_mkConst(v___x_32_, v___x_10_);
v___x_34_ = l_Lean_mkApp3(v___x_33_, v_origExpr_11_, v_a_22_, v___y_29_);
v___x_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_35_);
v___x_37_ = v___x_26_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v___x_35_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
}
else
{
lean_dec(v_a_22_);
lean_dec_ref(v_origExpr_11_);
lean_dec(v___x_10_);
lean_dec_ref(v___x_9_);
lean_dec_ref(v___x_8_);
lean_dec_ref(v___x_7_);
lean_dec_ref(v___x_6_);
lean_dec(v_width_3_);
return v___x_23_;
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec_ref(v_origExpr_11_);
lean_dec(v___x_10_);
lean_dec_ref(v___x_9_);
lean_dec_ref(v___x_8_);
lean_dec_ref(v___x_7_);
lean_dec_ref(v___x_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_width_3_);
v_a_42_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_21_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_21_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed(lean_object** _args){
lean_object* v_width_50_ = _args[0];
lean_object* v_expr_51_ = _args[1];
lean_object* v_a_52_ = _args[2];
lean_object* v___x_53_ = _args[3];
lean_object* v___x_54_ = _args[4];
lean_object* v___x_55_ = _args[5];
lean_object* v___x_56_ = _args[6];
lean_object* v___x_57_ = _args[7];
lean_object* v_origExpr_58_ = _args[8];
lean_object* v___y_59_ = _args[9];
lean_object* v___y_60_ = _args[10];
lean_object* v___y_61_ = _args[11];
lean_object* v___y_62_ = _args[12];
lean_object* v___y_63_ = _args[13];
lean_object* v___y_64_ = _args[14];
lean_object* v___y_65_ = _args[15];
lean_object* v___y_66_ = _args[16];
lean_object* v___y_67_ = _args[17];
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0(v_width_50_, v_expr_51_, v_a_52_, v___x_53_, v___x_54_, v___x_55_, v___x_56_, v___x_57_, v_origExpr_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
return v_res_68_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_box(0);
v___x_78_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__4));
v___x_79_ = l_Lean_mkConst(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_box(0);
v___x_92_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__11));
v___x_93_ = l_Lean_mkConst(v___x_92_, v___x_91_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1u);
v___x_95_ = l_Lean_mkNatLit(v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = l_Lean_mkNatLit(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(lean_object* v_origExpr_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; 
lean_inc_ref(v_origExpr_98_);
v___x_108_ = l_Lean_Meta_Sym_inferType(v_origExpr_98_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_178_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_178_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_178_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_178_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = l_Lean_Expr_cleanupAnnotations(v_a_109_);
v___x_114_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__1));
v___x_115_ = l_Lean_Expr_isConstOf(v___x_113_, v___x_114_);
lean_dec_ref(v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_118_; 
lean_dec_ref(v_origExpr_98_);
v___x_116_ = lean_box(0);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_116_);
v___x_118_ = v___x_111_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
lean_del_object(v___x_111_);
v___x_120_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2));
v___x_121_ = lean_box(0);
v___x_122_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__5);
lean_inc_ref(v_origExpr_98_);
v___x_123_ = l_Lean_Expr_app___override(v___x_122_, v_origExpr_98_);
v___x_124_ = l_Lean_Meta_Sym_shareCommonInc(v___x_123_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = 0;
v___x_128_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(v_a_125_, v___x_126_, v___x_127_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v_width_130_; lean_object* v_bvExpr_131_; lean_object* v_expr_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_a_129_);
lean_dec_ref_known(v___x_128_, 1);
v_width_130_ = lean_ctor_get(v_a_129_, 0);
lean_inc_n(v_width_130_, 2);
v_bvExpr_131_ = lean_ctor_get(v_a_129_, 1);
v_expr_132_ = lean_ctor_get(v_a_129_, 4);
lean_inc_ref_n(v_expr_132_, 2);
v___x_133_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_bvExpr_131_);
v___x_134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_134_, 0, v_width_130_);
lean_ctor_set(v___x_134_, 1, v_bvExpr_131_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
v___x_135_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6));
v___x_136_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7));
v___x_137_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8));
v___x_138_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12);
v___x_139_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__13);
v___x_140_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__14);
v___x_141_ = l_Lean_mkApp3(v___x_138_, v___x_139_, v_expr_132_, v___x_140_);
v___x_142_ = l_Lean_Meta_Sym_shareCommonInc(v___x_141_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___f_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
lean_inc_ref(v_origExpr_98_);
v___f_147_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___boxed), 18, 9);
lean_closure_set(v___f_147_, 0, v_width_130_);
lean_closure_set(v___f_147_, 1, v_expr_132_);
lean_closure_set(v___f_147_, 2, v_a_129_);
lean_closure_set(v___f_147_, 3, v___x_135_);
lean_closure_set(v___f_147_, 4, v___x_136_);
lean_closure_set(v___f_147_, 5, v___x_137_);
lean_closure_set(v___f_147_, 6, v___x_120_);
lean_closure_set(v___f_147_, 7, v___x_121_);
lean_closure_set(v___f_147_, 8, v_origExpr_98_);
v___x_148_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_148_, 0, v___x_134_);
lean_ctor_set(v___x_148_, 1, v_origExpr_98_);
lean_ctor_set(v___x_148_, 2, v___f_147_);
lean_ctor_set(v___x_148_, 3, v_a_143_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_149_);
v___x_151_ = v___x_145_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec_ref_known(v___x_134_, 3);
lean_dec_ref(v_expr_132_);
lean_dec(v_width_130_);
lean_dec(v_a_129_);
lean_dec_ref(v_origExpr_98_);
v_a_154_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_142_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_142_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec_ref(v_origExpr_98_);
v_a_162_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_128_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_128_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec_ref(v_origExpr_98_);
v_a_170_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_124_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_124_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec_ref(v_origExpr_98_);
v_a_179_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_108_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_108_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___boxed(lean_object* v_origExpr_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(v_origExpr_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(uint8_t v_pred_214_){
_start:
{
if (v_pred_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__1));
return v___x_215_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___closed__3));
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred___boxed(lean_object* v_pred_217_){
_start:
{
uint8_t v_pred_boxed_218_; lean_object* v_res_219_; 
v_pred_boxed_218_ = lean_unbox(v_pred_217_);
v_res_219_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(v_pred_boxed_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(lean_object* v___x_220_, lean_object* v_fst_221_, lean_object* v_fproof_222_, lean_object* v_snd_223_, lean_object* v_sproof_224_){
_start:
{
if (lean_obj_tag(v_fproof_222_) == 0)
{
lean_dec_ref(v_snd_223_);
if (lean_obj_tag(v_sproof_224_) == 0)
{
lean_object* v___x_225_; 
lean_dec_ref(v_fst_221_);
lean_dec(v___x_220_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
else
{
lean_object* v_val_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_235_; 
v_val_226_ = lean_ctor_get(v_sproof_224_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_sproof_224_);
if (v_isSharedCheck_235_ == 0)
{
v___x_228_ = v_sproof_224_;
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_val_226_);
lean_dec(v_sproof_224_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_235_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_220_, v_fst_221_);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v_val_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 0, v___x_231_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
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
lean_dec_ref(v_fst_221_);
if (lean_obj_tag(v_sproof_224_) == 0)
{
lean_object* v_val_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_245_; 
v_val_236_ = lean_ctor_get(v_fproof_222_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v_fproof_222_);
if (v_isSharedCheck_245_ == 0)
{
v___x_238_ = v_fproof_222_;
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_val_236_);
lean_dec(v_fproof_222_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_245_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_240_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(v___x_220_, v_snd_223_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_val_236_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_241_);
v___x_243_ = v___x_238_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
else
{
lean_object* v_val_246_; lean_object* v_val_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v_snd_223_);
lean_dec(v___x_220_);
v_val_246_ = lean_ctor_get(v_fproof_222_, 0);
lean_inc(v_val_246_);
lean_dec_ref_known(v_fproof_222_, 1);
v_val_247_ = lean_ctor_get(v_sproof_224_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_sproof_224_);
if (v_isSharedCheck_255_ == 0)
{
v___x_249_ = v_sproof_224_;
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_val_247_);
lean_dec(v_sproof_224_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_255_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v_val_246_);
lean_ctor_set(v___x_251_, 1, v_val_247_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 0, v___x_251_);
v___x_253_ = v___x_249_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(lean_object* v_width_256_, lean_object* v_expr_257_, lean_object* v_width_258_, lean_object* v_expr_259_, lean_object* v_lhs_260_, lean_object* v_rhs_261_, lean_object* v_congrThm_262_, lean_object* v___x_263_, lean_object* v___x_264_, lean_object* v_lhsExpr_265_, lean_object* v_rhsExpr_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v___x_276_; 
lean_inc(v_width_256_);
v___x_276_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_256_, v_expr_257_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_a_277_; lean_object* v___x_278_; 
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_276_, 1);
v___x_278_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_258_, v_expr_259_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_lhs_260_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_282_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_rhs_261_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_307_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_307_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_307_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; 
lean_inc(v_a_279_);
lean_inc(v_a_277_);
v___x_287_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_spec__0(v_width_256_, v_a_277_, v_a_281_, v_a_279_, v_a_283_);
if (lean_obj_tag(v___x_287_) == 1)
{
lean_object* v_val_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_302_; 
v_val_288_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_302_ == 0)
{
v___x_290_ = v___x_287_;
v_isShared_291_ = v_isSharedCheck_302_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_val_288_);
lean_dec(v___x_287_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_302_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v_fst_292_; lean_object* v_snd_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v_fst_292_ = lean_ctor_get(v_val_288_, 0);
lean_inc(v_fst_292_);
v_snd_293_ = lean_ctor_get(v_val_288_, 1);
lean_inc(v_snd_293_);
lean_dec(v_val_288_);
v___x_294_ = l_Lean_mkConst(v_congrThm_262_, v___x_263_);
v___x_295_ = l_Lean_mkApp7(v___x_294_, v___x_264_, v_lhsExpr_265_, v_rhsExpr_266_, v_a_277_, v_a_279_, v_fst_292_, v_snd_293_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_295_);
v___x_297_ = v___x_290_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_301_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_299_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_297_);
v___x_299_ = v___x_285_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_305_; 
lean_dec(v___x_287_);
lean_dec(v_a_279_);
lean_dec(v_a_277_);
lean_dec_ref(v_rhsExpr_266_);
lean_dec_ref(v_lhsExpr_265_);
lean_dec_ref(v___x_264_);
lean_dec(v___x_263_);
lean_dec(v_congrThm_262_);
v___x_303_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_303_);
v___x_305_ = v___x_285_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_303_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
else
{
lean_dec(v_a_281_);
lean_dec(v_a_279_);
lean_dec(v_a_277_);
lean_dec_ref(v_rhsExpr_266_);
lean_dec_ref(v_lhsExpr_265_);
lean_dec_ref(v___x_264_);
lean_dec(v___x_263_);
lean_dec(v_congrThm_262_);
lean_dec(v_width_256_);
return v___x_282_;
}
}
else
{
lean_dec(v_a_279_);
lean_dec(v_a_277_);
lean_dec_ref(v_rhsExpr_266_);
lean_dec_ref(v_lhsExpr_265_);
lean_dec_ref(v___x_264_);
lean_dec(v___x_263_);
lean_dec(v_congrThm_262_);
lean_dec_ref(v_rhs_261_);
lean_dec(v_width_256_);
return v___x_280_;
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec(v_a_277_);
lean_dec_ref(v_rhsExpr_266_);
lean_dec_ref(v_lhsExpr_265_);
lean_dec_ref(v___x_264_);
lean_dec(v___x_263_);
lean_dec(v_congrThm_262_);
lean_dec_ref(v_rhs_261_);
lean_dec_ref(v_lhs_260_);
lean_dec(v_width_256_);
v_a_308_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_278_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_278_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_rhsExpr_266_);
lean_dec_ref(v_lhsExpr_265_);
lean_dec_ref(v___x_264_);
lean_dec(v___x_263_);
lean_dec(v_congrThm_262_);
lean_dec_ref(v_rhs_261_);
lean_dec_ref(v_lhs_260_);
lean_dec_ref(v_expr_259_);
lean_dec(v_width_258_);
lean_dec(v_width_256_);
v_a_316_ = lean_ctor_get(v___x_276_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_276_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_276_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_276_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_width_324_ = _args[0];
lean_object* v_expr_325_ = _args[1];
lean_object* v_width_326_ = _args[2];
lean_object* v_expr_327_ = _args[3];
lean_object* v_lhs_328_ = _args[4];
lean_object* v_rhs_329_ = _args[5];
lean_object* v_congrThm_330_ = _args[6];
lean_object* v___x_331_ = _args[7];
lean_object* v___x_332_ = _args[8];
lean_object* v_lhsExpr_333_ = _args[9];
lean_object* v_rhsExpr_334_ = _args[10];
lean_object* v___y_335_ = _args[11];
lean_object* v___y_336_ = _args[12];
lean_object* v___y_337_ = _args[13];
lean_object* v___y_338_ = _args[14];
lean_object* v___y_339_ = _args[15];
lean_object* v___y_340_ = _args[16];
lean_object* v___y_341_ = _args[17];
lean_object* v___y_342_ = _args[18];
lean_object* v___y_343_ = _args[19];
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0(v_width_324_, v_expr_325_, v_width_326_, v_expr_327_, v_lhs_328_, v_rhs_329_, v_congrThm_330_, v___x_331_, v___x_332_, v_lhsExpr_333_, v_rhsExpr_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_344_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_box(0);
v___x_353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__1));
v___x_354_ = l_Lean_mkConst(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_box(0);
v___x_364_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__5));
v___x_365_ = l_Lean_mkConst(v___x_364_, v___x_363_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_373_ = lean_box(0);
v___x_374_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__8));
v___x_375_ = l_Lean_mkConst(v___x_374_, v___x_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(lean_object* v_lhs_376_, lean_object* v_rhs_377_, lean_object* v_lhsExpr_378_, lean_object* v_rhsExpr_379_, uint8_t v_pred_380_, lean_object* v_origExpr_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_width_389_; lean_object* v_bvExpr_390_; lean_object* v_expr_391_; lean_object* v_width_392_; lean_object* v_bvExpr_393_; lean_object* v_expr_394_; uint8_t v___x_395_; 
v_width_389_ = lean_ctor_get(v_lhs_376_, 0);
lean_inc(v_width_389_);
v_bvExpr_390_ = lean_ctor_get(v_lhs_376_, 1);
v_expr_391_ = lean_ctor_get(v_lhs_376_, 4);
lean_inc_ref(v_expr_391_);
v_width_392_ = lean_ctor_get(v_rhs_377_, 0);
lean_inc(v_width_392_);
v_bvExpr_393_ = lean_ctor_get(v_rhs_377_, 1);
v_expr_394_ = lean_ctor_get(v_rhs_377_, 4);
lean_inc_ref(v_expr_394_);
v___x_395_ = lean_nat_dec_eq(v_width_389_, v_width_392_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_dec_ref(v_expr_394_);
lean_dec(v_width_392_);
lean_dec_ref(v_expr_391_);
lean_dec(v_width_389_);
lean_dec_ref(v_origExpr_381_);
lean_dec_ref(v_rhsExpr_379_);
lean_dec_ref(v_lhsExpr_378_);
lean_dec_ref(v_rhs_377_);
lean_dec_ref(v_lhs_376_);
v___x_396_ = lean_box(0);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
else
{
lean_object* v_congrThm_398_; lean_object* v_bvExpr_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___f_403_; lean_object* v___y_405_; 
v_congrThm_398_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred_0__Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred_congrThmOfBinPred(v_pred_380_);
lean_inc_ref(v_bvExpr_393_);
lean_inc_ref(v_bvExpr_390_);
lean_inc_n(v_width_389_, 2);
v_bvExpr_399_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_bvExpr_399_, 0, v_width_389_);
lean_ctor_set(v_bvExpr_399_, 1, v_bvExpr_390_);
lean_ctor_set(v_bvExpr_399_, 2, v_bvExpr_393_);
lean_ctor_set_uint8(v_bvExpr_399_, sizeof(void*)*3, v_pred_380_);
v___x_400_ = lean_box(0);
v___x_401_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__2);
v___x_402_ = l_Lean_mkNatLit(v_width_389_);
lean_inc_ref(v___x_402_);
lean_inc_ref(v_expr_394_);
lean_inc_ref(v_expr_391_);
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___lam__0___boxed), 20, 11);
lean_closure_set(v___f_403_, 0, v_width_389_);
lean_closure_set(v___f_403_, 1, v_expr_391_);
lean_closure_set(v___f_403_, 2, v_width_392_);
lean_closure_set(v___f_403_, 3, v_expr_394_);
lean_closure_set(v___f_403_, 4, v_lhs_376_);
lean_closure_set(v___f_403_, 5, v_rhs_377_);
lean_closure_set(v___f_403_, 6, v_congrThm_398_);
lean_closure_set(v___f_403_, 7, v___x_400_);
lean_closure_set(v___f_403_, 8, v___x_402_);
lean_closure_set(v___f_403_, 9, v_lhsExpr_378_);
lean_closure_set(v___f_403_, 10, v_rhsExpr_379_);
if (v_pred_380_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__6);
v___y_405_ = v___x_426_;
goto v___jp_404_;
}
else
{
lean_object* v___x_427_; 
v___x_427_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___closed__9);
v___y_405_ = v___x_427_;
goto v___jp_404_;
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_inc_ref(v___y_405_);
v___x_406_ = l_Lean_mkApp4(v___x_401_, v___x_402_, v_expr_391_, v___y_405_, v_expr_394_);
v___x_407_ = l_Lean_Meta_Sym_shareCommonInc(v___x_406_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_417_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_417_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_417_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_412_, 0, v_bvExpr_399_);
lean_ctor_set(v___x_412_, 1, v_origExpr_381_);
lean_ctor_set(v___x_412_, 2, v___f_403_);
lean_ctor_set(v___x_412_, 3, v_a_408_);
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v___f_403_);
lean_dec_ref_known(v_bvExpr_399_, 3);
lean_dec_ref(v_origExpr_381_);
v_a_418_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_407_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_407_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg___boxed(lean_object* v_lhs_428_, lean_object* v_rhs_429_, lean_object* v_lhsExpr_430_, lean_object* v_rhsExpr_431_, lean_object* v_pred_432_, lean_object* v_origExpr_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
uint8_t v_pred_boxed_441_; lean_object* v_res_442_; 
v_pred_boxed_441_ = lean_unbox(v_pred_432_);
v_res_442_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_lhs_428_, v_rhs_429_, v_lhsExpr_430_, v_rhsExpr_431_, v_pred_boxed_441_, v_origExpr_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(lean_object* v_lhs_443_, lean_object* v_rhs_444_, lean_object* v_lhsExpr_445_, lean_object* v_rhsExpr_446_, uint8_t v_pred_447_, lean_object* v_origExpr_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___redArg(v_lhs_443_, v_rhs_444_, v_lhsExpr_445_, v_rhsExpr_446_, v_pred_447_, v_origExpr_448_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred___boxed(lean_object* v_lhs_459_, lean_object* v_rhs_460_, lean_object* v_lhsExpr_461_, lean_object* v_rhsExpr_462_, lean_object* v_pred_463_, lean_object* v_origExpr_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
uint8_t v_pred_boxed_474_; lean_object* v_res_475_; 
v_pred_boxed_474_ = lean_unbox(v_pred_463_);
v_res_475_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkBinPred(v_lhs_459_, v_rhs_460_, v_lhsExpr_461_, v_rhsExpr_462_, v_pred_boxed_474_, v_origExpr_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_a_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_a_467_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(lean_object* v_sub_477_, lean_object* v_width_478_, lean_object* v_expr_479_, lean_object* v___x_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v___x_483_, lean_object* v_idxExpr_484_, lean_object* v___x_485_, lean_object* v_subExpr_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_sub_477_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_536_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_536_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_536_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_536_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
if (lean_obj_tag(v_a_497_) == 1)
{
lean_object* v_val_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_531_; 
lean_del_object(v___x_499_);
v_val_501_ = lean_ctor_get(v_a_497_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_531_ == 0)
{
v___x_503_ = v_a_497_;
v_isShared_504_ = v_isSharedCheck_531_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_val_501_);
lean_dec(v_a_497_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_531_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_width_478_, v_expr_479_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_522_; 
v_a_506_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_522_ == 0)
{
v___x_508_ = v___x_505_;
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_505_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_522_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_510_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___lam__0___closed__0));
v___x_511_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__2));
v___x_512_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___closed__0));
v___x_513_ = l_Lean_Name_mkStr6(v___x_480_, v___x_481_, v___x_482_, v___x_510_, v___x_511_, v___x_512_);
v___x_514_ = l_Lean_mkConst(v___x_513_, v___x_483_);
v___x_515_ = l_Lean_mkApp5(v___x_514_, v_idxExpr_484_, v___x_485_, v_subExpr_486_, v_a_506_, v_val_501_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_515_);
v___x_517_ = v___x_503_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_521_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_519_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 0, v___x_517_);
v___x_519_ = v___x_508_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_del_object(v___x_503_);
lean_dec(v_val_501_);
lean_dec_ref(v_subExpr_486_);
lean_dec_ref(v___x_485_);
lean_dec_ref(v_idxExpr_484_);
lean_dec(v___x_483_);
lean_dec_ref(v___x_482_);
lean_dec_ref(v___x_481_);
lean_dec_ref(v___x_480_);
v_a_523_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_505_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_505_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_534_; 
lean_dec(v_a_497_);
lean_dec_ref(v_subExpr_486_);
lean_dec_ref(v___x_485_);
lean_dec_ref(v_idxExpr_484_);
lean_dec(v___x_483_);
lean_dec_ref(v___x_482_);
lean_dec_ref(v___x_481_);
lean_dec_ref(v___x_480_);
lean_dec_ref(v_expr_479_);
lean_dec(v_width_478_);
v___x_532_ = lean_box(0);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_532_);
v___x_534_ = v___x_499_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_532_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
else
{
lean_dec_ref(v_subExpr_486_);
lean_dec_ref(v___x_485_);
lean_dec_ref(v_idxExpr_484_);
lean_dec(v___x_483_);
lean_dec_ref(v___x_482_);
lean_dec_ref(v___x_481_);
lean_dec_ref(v___x_480_);
lean_dec_ref(v_expr_479_);
lean_dec(v_width_478_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_sub_537_ = _args[0];
lean_object* v_width_538_ = _args[1];
lean_object* v_expr_539_ = _args[2];
lean_object* v___x_540_ = _args[3];
lean_object* v___x_541_ = _args[4];
lean_object* v___x_542_ = _args[5];
lean_object* v___x_543_ = _args[6];
lean_object* v_idxExpr_544_ = _args[7];
lean_object* v___x_545_ = _args[8];
lean_object* v_subExpr_546_ = _args[9];
lean_object* v___y_547_ = _args[10];
lean_object* v___y_548_ = _args[11];
lean_object* v___y_549_ = _args[12];
lean_object* v___y_550_ = _args[13];
lean_object* v___y_551_ = _args[14];
lean_object* v___y_552_ = _args[15];
lean_object* v___y_553_ = _args[16];
lean_object* v___y_554_ = _args[17];
lean_object* v___y_555_ = _args[18];
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0(v_sub_537_, v_width_538_, v_expr_539_, v___x_540_, v___x_541_, v___x_542_, v___x_543_, v_idxExpr_544_, v___x_545_, v_subExpr_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(lean_object* v_sub_557_, lean_object* v_subExpr_558_, lean_object* v_idx_559_, lean_object* v_origExpr_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_width_568_; lean_object* v_bvExpr_569_; lean_object* v_expr_570_; lean_object* v_bvExpr_571_; lean_object* v_idxExpr_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v_width_568_ = lean_ctor_get(v_sub_557_, 0);
lean_inc_n(v_width_568_, 3);
v_bvExpr_569_ = lean_ctor_get(v_sub_557_, 1);
v_expr_570_ = lean_ctor_get(v_sub_557_, 4);
lean_inc_ref_n(v_expr_570_, 2);
lean_inc(v_idx_559_);
lean_inc_ref(v_bvExpr_569_);
v_bvExpr_571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_bvExpr_571_, 0, v_width_568_);
lean_ctor_set(v_bvExpr_571_, 1, v_bvExpr_569_);
lean_ctor_set(v_bvExpr_571_, 2, v_idx_559_);
v_idxExpr_572_ = l_Lean_mkNatLit(v_idx_559_);
v___x_573_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__6));
v___x_574_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__7));
v___x_575_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__8));
v___x_576_ = lean_box(0);
v___x_577_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom___closed__12);
v___x_578_ = l_Lean_mkNatLit(v_width_568_);
lean_inc_ref(v_idxExpr_572_);
lean_inc_ref(v___x_578_);
v___x_579_ = l_Lean_mkApp3(v___x_577_, v___x_578_, v_expr_570_, v_idxExpr_572_);
v___x_580_ = l_Lean_Meta_Sym_shareCommonInc(v___x_579_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_590_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_590_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_590_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___f_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v___f_585_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___lam__0___boxed), 19, 10);
lean_closure_set(v___f_585_, 0, v_sub_557_);
lean_closure_set(v___f_585_, 1, v_width_568_);
lean_closure_set(v___f_585_, 2, v_expr_570_);
lean_closure_set(v___f_585_, 3, v___x_573_);
lean_closure_set(v___f_585_, 4, v___x_574_);
lean_closure_set(v___f_585_, 5, v___x_575_);
lean_closure_set(v___f_585_, 6, v___x_576_);
lean_closure_set(v___f_585_, 7, v_idxExpr_572_);
lean_closure_set(v___f_585_, 8, v___x_578_);
lean_closure_set(v___f_585_, 9, v_subExpr_558_);
v___x_586_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_586_, 0, v_bvExpr_571_);
lean_ctor_set(v___x_586_, 1, v_origExpr_560_);
lean_ctor_set(v___x_586_, 2, v___f_585_);
lean_ctor_set(v___x_586_, 3, v_a_581_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec_ref(v___x_578_);
lean_dec_ref(v_idxExpr_572_);
lean_dec_ref_known(v_bvExpr_571_, 3);
lean_dec_ref(v_expr_570_);
lean_dec(v_width_568_);
lean_dec_ref(v_origExpr_560_);
lean_dec_ref(v_subExpr_558_);
lean_dec_ref(v_sub_557_);
v_a_591_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_580_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_580_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg___boxed(lean_object* v_sub_599_, lean_object* v_subExpr_600_, lean_object* v_idx_601_, lean_object* v_origExpr_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(v_sub_599_, v_subExpr_600_, v_idx_601_, v_origExpr_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(lean_object* v_sub_611_, lean_object* v_subExpr_612_, lean_object* v_idx_613_, lean_object* v_origExpr_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___redArg(v_sub_611_, v_subExpr_612_, v_idx_613_, v_origExpr_614_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD___boxed(lean_object* v_sub_625_, lean_object* v_subExpr_626_, lean_object* v_idx_627_, lean_object* v_origExpr_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_mkGetLsbD(v_sub_625_, v_subExpr_626_, v_idx_627_, v_origExpr_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
lean_dec(v_a_634_);
lean_dec_ref(v_a_633_);
lean_dec(v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
return v_res_638_;
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

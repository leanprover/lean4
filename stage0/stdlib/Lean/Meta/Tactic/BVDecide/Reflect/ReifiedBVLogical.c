// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Basic import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVPred import Std.Tactic.BVDecide.Reflect
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "BVLogicalExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(81, 172, 123, 74, 237, 247, 157, 191)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BoolExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "literal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 170, 215, 35, 43, 27, 202, 11)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 184, 12, 163, 38, 128, 83, 107)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "and_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 74, 55, 212, 47, 213, 221, 101)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(18, 149, 13, 143, 231, 41, 150, 146)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "xor_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 74, 55, 212, 47, 213, 221, 101)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__3_value),LEAN_SCALAR_PTR_LITERAL(143, 142, 245, 112, 164, 111, 120, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "beq_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 74, 55, 212, 47, 213, 221, 101)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__5_value),LEAN_SCALAR_PTR_LITERAL(101, 115, 64, 1, 88, 223, 29, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "or_congr"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 74, 55, 212, 47, 213, 221, 101)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__7_value),LEAN_SCALAR_PTR_LITERAL(183, 116, 6, 33, 14, 220, 127, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(65, 48, 52, 229, 233, 139, 247, 222)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 125, 195, 121, 220, 103, 239, 120)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(64, 67, 164, 147, 7, 85, 189, 57)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(208, 118, 173, 79, 191, 184, 148, 203)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(37, 170, 13, 59, 155, 6, 165, 62)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 134, 245, 64, 53, 182, 217, 215)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cond_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 47, 143, 42, 137, 9, 112, 75)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(1u);
v___x_7_ = l_Lean_Level_ofNat(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__3);
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4);
v___x_12_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__2));
v___x_13_ = l_Lean_mkConst(v___x_12_, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_box(0);
v___x_18_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__7));
v___x_19_ = l_Lean_mkConst(v___x_18_, v___x_17_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(lean_object* v_expr_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__5);
v___x_22_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8);
v___x_23_ = l_Lean_mkAppB(v___x_21_, v___x_22_, v_expr_20_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__4);
v___x_29_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__1));
v___x_30_ = l_Lean_mkConst(v___x_29_, v___x_28_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(lean_object* v_x_31_, lean_object* v_y_32_, lean_object* v_z_33_, lean_object* v_hxy_34_, lean_object* v_hyz_35_){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans___closed__2);
v___x_37_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__8);
v___x_38_ = l_Lean_mkApp6(v___x_36_, v___x_37_, v_x_31_, v_y_32_, v_z_33_, v_hxy_34_, v_hyz_35_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__5));
v___x_52_ = l_Lean_mkConst(v___x_51_, v___x_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object* v_expr_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v_a_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_a_64_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_a_64_);
lean_dec_ref_known(v___x_63_, 1);
v___x_65_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6);
v___x_66_ = l_Lean_mkAppB(v___x_65_, v_a_64_, v_expr_53_);
v___x_67_ = l_Lean_Meta_Sym_shareCommonInc(v___x_66_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_);
return v___x_67_;
}
else
{
lean_dec_ref(v_expr_53_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___boxed(lean_object* v_expr_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
lean_dec(v_a_72_);
lean_dec_ref(v_a_71_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
return v_res_78_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2));
v___x_89_ = l_Lean_mkConst(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_box(0);
v___x_97_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__5));
v___x_98_ = l_Lean_mkConst(v___x_97_, v___x_96_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(lean_object* v_bvPred_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_bvPred_107_; lean_object* v_originalExpr_108_; lean_object* v_expr_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_bvPred_107_ = lean_ctor_get(v_bvPred_99_, 0);
v_originalExpr_108_ = lean_ctor_get(v_bvPred_99_, 1);
lean_inc_ref(v_originalExpr_108_);
v_expr_109_ = lean_ctor_get(v_bvPred_99_, 3);
v___x_110_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__3);
v___x_111_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6);
lean_inc_ref(v_expr_109_);
v___x_112_ = l_Lean_mkAppB(v___x_110_, v___x_111_, v_expr_109_);
v___x_113_ = l_Lean_Meta_Sym_shareCommonInc(v___x_112_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_124_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_124_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_boolExpr_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
lean_inc_ref(v_bvPred_107_);
v_boolExpr_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_boolExpr_118_, 0, v_bvPred_107_);
v___x_119_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed), 10, 1);
lean_closure_set(v___x_119_, 0, v_bvPred_99_);
v___x_120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_120_, 0, v_boolExpr_118_);
lean_ctor_set(v___x_120_, 1, v_originalExpr_108_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_ctor_set(v___x_120_, 3, v_a_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_120_);
v___x_122_ = v___x_116_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_originalExpr_108_);
lean_dec_ref(v_bvPred_99_);
v_a_125_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_113_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_113_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___boxed(lean_object* v_bvPred_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_bvPred_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(lean_object* v_bvPred_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_bvPred_142_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___boxed(lean_object* v_bvPred_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(v_bvPred_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_);
lean_dec(v_a_161_);
lean_dec_ref(v_a_160_);
lean_dec(v_a_159_);
lean_dec_ref(v_a_158_);
lean_dec(v_a_157_);
lean_dec_ref(v_a_156_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(lean_object* v_t_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_boolAtom(v_t_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_208_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_208_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_208_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_208_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
if (lean_obj_tag(v_a_175_) == 1)
{
lean_object* v_val_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_203_; 
lean_del_object(v___x_177_);
v_val_179_ = lean_ctor_get(v_a_175_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_a_175_);
if (v_isSharedCheck_203_ == 0)
{
v___x_181_ = v_a_175_;
v_isShared_182_ = v_isSharedCheck_203_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_val_179_);
lean_dec(v_a_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_203_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_val_179_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_194_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_194_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_194_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v_a_184_);
v___x_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_193_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
lean_object* v___x_191_; 
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 0, v___x_189_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_del_object(v___x_181_);
v_a_195_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_183_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_183_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v___x_204_; lean_object* v___x_206_; 
lean_dec(v_a_175_);
v___x_204_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_204_);
v___x_206_ = v___x_177_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v___x_204_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
v_a_209_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_174_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_174_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom___boxed(lean_object* v_t_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_boolAtom(v_t_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(lean_object* v___x_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_228_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed(lean_object* v___x_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(v___x_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_249_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
v___x_267_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5));
v___x_268_ = l_Lean_mkConst(v___x_267_, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
v___x_274_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8));
v___x_275_ = l_Lean_mkConst(v___x_274_, v___x_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(uint8_t v_val_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v_boolExpr_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___y_288_; 
v_boolExpr_284_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v_boolExpr_284_, 0, v_val_276_);
v___x_285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2);
v___x_286_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6);
if (v_val_276_ == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6);
v___y_288_ = v___x_319_;
goto v___jp_287_;
}
else
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9);
v___y_288_ = v___x_320_;
goto v___jp_287_;
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_inc_ref(v___y_288_);
v___x_289_ = l_Lean_mkAppB(v___x_285_, v___x_286_, v___y_288_);
v___x_290_ = l_Lean_Meta_Sym_shareCommonInc(v___x_289_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_290_, 1);
lean_inc_ref(v___y_288_);
v___x_292_ = l_Lean_Meta_Sym_shareCommonInc(v___y_288_, v_a_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_);
if (lean_obj_tag(v___x_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_302_; 
v_a_293_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_302_ == 0)
{
v___x_295_ = v___x_292_;
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_292_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_302_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___f_297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3));
v___x_298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_298_, 0, v_boolExpr_284_);
lean_ctor_set(v___x_298_, 1, v_a_293_);
lean_ctor_set(v___x_298_, 2, v___f_297_);
lean_ctor_set(v___x_298_, 3, v_a_291_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_298_);
v___x_300_ = v___x_295_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec(v_a_291_);
lean_dec_ref_known(v_boolExpr_284_, 0);
v_a_303_ = lean_ctor_get(v___x_292_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_292_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_292_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_292_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
lean_dec_ref_known(v_boolExpr_284_, 0);
v_a_311_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_290_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_290_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___boxed(lean_object* v_val_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
uint8_t v_val_boxed_329_; lean_object* v_res_330_; 
v_val_boxed_329_ = lean_unbox(v_val_321_);
v_res_330_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v_val_boxed_329_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(uint8_t v_val_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v_val_331_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___boxed(lean_object* v_val_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
uint8_t v_val_boxed_352_; lean_object* v_res_353_; 
v_val_boxed_352_ = lean_unbox(v_val_342_);
v_res_353_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(v_val_boxed_352_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
lean_dec(v_a_350_);
lean_dec_ref(v_a_349_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(uint8_t v_gate_387_){
_start:
{
switch(v_gate_387_)
{
case 0:
{
lean_object* v___x_388_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2));
return v___x_388_;
}
case 1:
{
lean_object* v___x_389_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4));
return v___x_389_;
}
case 2:
{
lean_object* v___x_390_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6));
return v___x_390_;
}
default: 
{
lean_object* v___x_391_; 
v___x_391_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8));
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___boxed(lean_object* v_gate_392_){
_start:
{
uint8_t v_gate_boxed_393_; lean_object* v_res_394_; 
v_gate_boxed_393_ = lean_unbox(v_gate_392_);
v_res_394_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(v_gate_boxed_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(lean_object* v_fst_395_, lean_object* v_fproof_396_, lean_object* v_snd_397_, lean_object* v_sproof_398_){
_start:
{
if (lean_obj_tag(v_fproof_396_) == 0)
{
lean_dec_ref(v_snd_397_);
if (lean_obj_tag(v_sproof_398_) == 0)
{
lean_object* v___x_399_; 
lean_dec_ref(v_fst_395_);
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
lean_object* v_val_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
v_val_400_ = lean_ctor_get(v_sproof_398_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_sproof_398_);
if (v_isSharedCheck_409_ == 0)
{
v___x_402_ = v_sproof_398_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_val_400_);
lean_dec(v_sproof_398_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_404_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_fst_395_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_val_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_405_);
v___x_407_ = v___x_402_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
else
{
lean_dec_ref(v_fst_395_);
if (lean_obj_tag(v_sproof_398_) == 0)
{
lean_object* v_val_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_419_; 
v_val_410_ = lean_ctor_get(v_fproof_396_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v_fproof_396_);
if (v_isSharedCheck_419_ == 0)
{
v___x_412_ = v_fproof_396_;
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_val_410_);
lean_dec(v_fproof_396_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_snd_397_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_val_410_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_object* v_val_420_; lean_object* v_val_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
lean_dec_ref(v_snd_397_);
v_val_420_ = lean_ctor_get(v_fproof_396_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_fproof_396_, 1);
v_val_421_ = lean_ctor_get(v_sproof_398_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_sproof_398_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v_sproof_398_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_val_421_);
lean_dec(v_sproof_398_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_val_420_);
lean_ctor_set(v___x_425_, 1, v_val_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(lean_object* v_expr_430_, lean_object* v_expr_431_, lean_object* v_lhs_432_, lean_object* v_rhs_433_, lean_object* v_congrThm_434_, lean_object* v___x_435_, lean_object* v_lhsExpr_436_, lean_object* v_rhsExpr_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_430_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_431_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_451_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_lhs_432_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_453_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_a_452_);
lean_dec_ref_known(v___x_451_, 1);
v___x_453_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_rhs_433_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
if (lean_obj_tag(v___x_453_) == 0)
{
lean_object* v_a_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_478_; 
v_a_454_ = lean_ctor_get(v___x_453_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_453_);
if (v_isSharedCheck_478_ == 0)
{
v___x_456_ = v___x_453_;
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_a_454_);
lean_dec(v___x_453_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_478_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; 
lean_inc(v_a_450_);
lean_inc(v_a_448_);
v___x_458_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_a_448_, v_a_452_, v_a_450_, v_a_454_);
if (lean_obj_tag(v___x_458_) == 1)
{
lean_object* v_val_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_473_; 
v_val_459_ = lean_ctor_get(v___x_458_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_458_);
if (v_isSharedCheck_473_ == 0)
{
v___x_461_ = v___x_458_;
v_isShared_462_ = v_isSharedCheck_473_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_val_459_);
lean_dec(v___x_458_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_473_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v_fst_463_; lean_object* v_snd_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v_fst_463_ = lean_ctor_get(v_val_459_, 0);
lean_inc(v_fst_463_);
v_snd_464_ = lean_ctor_get(v_val_459_, 1);
lean_inc(v_snd_464_);
lean_dec(v_val_459_);
v___x_465_ = l_Lean_mkConst(v_congrThm_434_, v___x_435_);
v___x_466_ = l_Lean_mkApp6(v___x_465_, v_lhsExpr_436_, v_rhsExpr_437_, v_a_448_, v_a_450_, v_fst_463_, v_snd_464_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_466_);
v___x_468_ = v___x_461_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_466_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_468_);
v___x_470_ = v___x_456_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v___x_474_; lean_object* v___x_476_; 
lean_dec(v___x_458_);
lean_dec(v_a_450_);
lean_dec(v_a_448_);
lean_dec_ref(v_rhsExpr_437_);
lean_dec_ref(v_lhsExpr_436_);
lean_dec(v___x_435_);
lean_dec(v_congrThm_434_);
v___x_474_ = lean_box(0);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_474_);
v___x_476_ = v___x_456_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
else
{
lean_dec(v_a_452_);
lean_dec(v_a_450_);
lean_dec(v_a_448_);
lean_dec_ref(v_rhsExpr_437_);
lean_dec_ref(v_lhsExpr_436_);
lean_dec(v___x_435_);
lean_dec(v_congrThm_434_);
return v___x_453_;
}
}
else
{
lean_dec(v_a_450_);
lean_dec(v_a_448_);
lean_dec_ref(v_rhsExpr_437_);
lean_dec_ref(v_lhsExpr_436_);
lean_dec(v___x_435_);
lean_dec(v_congrThm_434_);
lean_dec_ref(v_rhs_433_);
return v___x_451_;
}
}
else
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
lean_dec(v_a_448_);
lean_dec_ref(v_rhsExpr_437_);
lean_dec_ref(v_lhsExpr_436_);
lean_dec(v___x_435_);
lean_dec(v_congrThm_434_);
lean_dec_ref(v_rhs_433_);
lean_dec_ref(v_lhs_432_);
v_a_479_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_449_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_449_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
lean_dec_ref(v_rhsExpr_437_);
lean_dec_ref(v_lhsExpr_436_);
lean_dec(v___x_435_);
lean_dec(v_congrThm_434_);
lean_dec_ref(v_rhs_433_);
lean_dec_ref(v_lhs_432_);
lean_dec_ref(v_expr_431_);
v_a_487_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_447_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_447_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_495_ = _args[0];
lean_object* v_expr_496_ = _args[1];
lean_object* v_lhs_497_ = _args[2];
lean_object* v_rhs_498_ = _args[3];
lean_object* v_congrThm_499_ = _args[4];
lean_object* v___x_500_ = _args[5];
lean_object* v_lhsExpr_501_ = _args[6];
lean_object* v_rhsExpr_502_ = _args[7];
lean_object* v___y_503_ = _args[8];
lean_object* v___y_504_ = _args[9];
lean_object* v___y_505_ = _args[10];
lean_object* v___y_506_ = _args[11];
lean_object* v___y_507_ = _args[12];
lean_object* v___y_508_ = _args[13];
lean_object* v___y_509_ = _args[14];
lean_object* v___y_510_ = _args[15];
lean_object* v___y_511_ = _args[16];
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(v_expr_495_, v_expr_496_, v_lhs_497_, v_rhs_498_, v_congrThm_499_, v___x_500_, v_lhsExpr_501_, v_rhsExpr_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_512_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_box(0);
v___x_521_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1));
v___x_522_ = l_Lean_mkConst(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6(void){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_box(0);
v___x_532_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5));
v___x_533_ = l_Lean_mkConst(v___x_532_, v___x_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_box(0);
v___x_542_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8));
v___x_543_ = l_Lean_mkConst(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_box(0);
v___x_552_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11));
v___x_553_ = l_Lean_mkConst(v___x_552_, v___x_551_);
return v___x_553_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_box(0);
v___x_562_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14));
v___x_563_ = l_Lean_mkConst(v___x_562_, v___x_561_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(lean_object* v_lhs_564_, lean_object* v_rhs_565_, lean_object* v_lhsExpr_566_, lean_object* v_rhsExpr_567_, uint8_t v_gate_568_, lean_object* v_origExpr_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_bvExpr_577_; lean_object* v_expr_578_; lean_object* v_bvExpr_579_; lean_object* v_expr_580_; lean_object* v_congrThm_581_; lean_object* v_boolExpr_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___y_588_; 
v_bvExpr_577_ = lean_ctor_get(v_lhs_564_, 0);
v_expr_578_ = lean_ctor_get(v_lhs_564_, 3);
lean_inc_ref_n(v_expr_578_, 2);
v_bvExpr_579_ = lean_ctor_get(v_rhs_565_, 0);
v_expr_580_ = lean_ctor_get(v_rhs_565_, 3);
lean_inc_ref_n(v_expr_580_, 2);
v_congrThm_581_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(v_gate_568_);
lean_inc_ref(v_bvExpr_579_);
lean_inc_ref(v_bvExpr_577_);
v_boolExpr_582_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_boolExpr_582_, 0, v_bvExpr_577_);
lean_ctor_set(v_boolExpr_582_, 1, v_bvExpr_579_);
lean_ctor_set_uint8(v_boolExpr_582_, sizeof(void*)*2, v_gate_568_);
v___x_583_ = lean_box(0);
v___f_584_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed), 17, 8);
lean_closure_set(v___f_584_, 0, v_expr_578_);
lean_closure_set(v___f_584_, 1, v_expr_580_);
lean_closure_set(v___f_584_, 2, v_lhs_564_);
lean_closure_set(v___f_584_, 3, v_rhs_565_);
lean_closure_set(v___f_584_, 4, v_congrThm_581_);
lean_closure_set(v___f_584_, 5, v___x_583_);
lean_closure_set(v___f_584_, 6, v_lhsExpr_566_);
lean_closure_set(v___f_584_, 7, v_rhsExpr_567_);
v___x_585_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2);
v___x_586_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6);
switch(v_gate_568_)
{
case 0:
{
lean_object* v___x_608_; 
v___x_608_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6);
v___y_588_ = v___x_608_;
goto v___jp_587_;
}
case 1:
{
lean_object* v___x_609_; 
v___x_609_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9);
v___y_588_ = v___x_609_;
goto v___jp_587_;
}
case 2:
{
lean_object* v___x_610_; 
v___x_610_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12);
v___y_588_ = v___x_610_;
goto v___jp_587_;
}
default: 
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15);
v___y_588_ = v___x_611_;
goto v___jp_587_;
}
}
v___jp_587_:
{
lean_object* v___x_589_; lean_object* v___x_590_; 
lean_inc_ref(v___y_588_);
v___x_589_ = l_Lean_mkApp4(v___x_585_, v___x_586_, v___y_588_, v_expr_578_, v_expr_580_);
v___x_590_ = l_Lean_Meta_Sym_shareCommonInc(v___x_589_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_599_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_599_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_599_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_595_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_595_, 0, v_boolExpr_582_);
lean_ctor_set(v___x_595_, 1, v_origExpr_569_);
lean_ctor_set(v___x_595_, 2, v___f_584_);
lean_ctor_set(v___x_595_, 3, v_a_591_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_595_);
v___x_597_ = v___x_593_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec_ref(v___f_584_);
lean_dec_ref_known(v_boolExpr_582_, 2);
lean_dec_ref(v_origExpr_569_);
v_a_600_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_590_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_590_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___boxed(lean_object* v_lhs_612_, lean_object* v_rhs_613_, lean_object* v_lhsExpr_614_, lean_object* v_rhsExpr_615_, lean_object* v_gate_616_, lean_object* v_origExpr_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
uint8_t v_gate_boxed_625_; lean_object* v_res_626_; 
v_gate_boxed_625_ = lean_unbox(v_gate_616_);
v_res_626_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_lhs_612_, v_rhs_613_, v_lhsExpr_614_, v_rhsExpr_615_, v_gate_boxed_625_, v_origExpr_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(lean_object* v_lhs_627_, lean_object* v_rhs_628_, lean_object* v_lhsExpr_629_, lean_object* v_rhsExpr_630_, uint8_t v_gate_631_, lean_object* v_origExpr_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_lhs_627_, v_rhs_628_, v_lhsExpr_629_, v_rhsExpr_630_, v_gate_631_, v_origExpr_632_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___boxed(lean_object* v_lhs_643_, lean_object* v_rhs_644_, lean_object* v_lhsExpr_645_, lean_object* v_rhsExpr_646_, lean_object* v_gate_647_, lean_object* v_origExpr_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_){
_start:
{
uint8_t v_gate_boxed_658_; lean_object* v_res_659_; 
v_gate_boxed_658_ = lean_unbox(v_gate_647_);
v_res_659_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(v_lhs_643_, v_rhs_644_, v_lhsExpr_645_, v_rhsExpr_646_, v_gate_boxed_658_, v_origExpr_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_);
lean_dec(v_a_656_);
lean_dec_ref(v_a_655_);
lean_dec(v_a_654_);
lean_dec_ref(v_a_653_);
lean_dec(v_a_652_);
lean_dec_ref(v_a_651_);
lean_dec(v_a_650_);
lean_dec_ref(v_a_649_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(lean_object* v_sub_661_, lean_object* v_expr_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v_subExpr_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_sub_661_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_717_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_717_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_717_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_717_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
if (lean_obj_tag(v_a_678_) == 1)
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_712_; 
lean_del_object(v___x_680_);
v_val_682_ = lean_ctor_get(v_a_678_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_a_678_);
if (v_isSharedCheck_712_ == 0)
{
v___x_684_ = v_a_678_;
v_isShared_685_ = v_isSharedCheck_712_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v_a_678_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_712_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_686_; 
v___x_686_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_662_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_703_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_703_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_703_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0));
v___x_692_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6));
v___x_693_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0));
v___x_694_ = l_Lean_Name_mkStr6(v___x_663_, v___x_664_, v___x_665_, v___x_691_, v___x_692_, v___x_693_);
v___x_695_ = l_Lean_mkConst(v___x_694_, v___x_666_);
v___x_696_ = l_Lean_mkApp3(v___x_695_, v_subExpr_667_, v_a_687_, v_val_682_);
if (v_isShared_685_ == 0)
{
lean_ctor_set(v___x_684_, 0, v___x_696_);
v___x_698_ = v___x_684_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_702_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_700_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_698_);
v___x_700_ = v___x_689_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_del_object(v___x_684_);
lean_dec(v_val_682_);
lean_dec_ref(v_subExpr_667_);
lean_dec(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec_ref(v___x_663_);
v_a_704_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_686_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_686_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_715_; 
lean_dec(v_a_678_);
lean_dec_ref(v_subExpr_667_);
lean_dec(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec_ref(v_expr_662_);
v___x_713_ = lean_box(0);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_713_);
v___x_715_ = v___x_680_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_dec_ref(v_subExpr_667_);
lean_dec(v___x_666_);
lean_dec_ref(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec_ref(v_expr_662_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed(lean_object* v_sub_718_, lean_object* v_expr_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v___x_723_, lean_object* v_subExpr_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(v_sub_718_, v_expr_719_, v___x_720_, v___x_721_, v___x_722_, v___x_723_, v_subExpr_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_box(0);
v___x_743_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1));
v___x_744_ = l_Lean_mkConst(v___x_743_, v___x_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(lean_object* v_sub_745_, lean_object* v_subExpr_746_, lean_object* v_origExpr_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_bvExpr_755_; lean_object* v_expr_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_bvExpr_755_ = lean_ctor_get(v_sub_745_, 0);
lean_inc_ref(v_bvExpr_755_);
v_expr_756_ = lean_ctor_get(v_sub_745_, 3);
lean_inc_ref_n(v_expr_756_, 2);
v___x_757_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0));
v___x_758_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1));
v___x_759_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2));
v___x_760_ = lean_box(0);
v___x_761_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2);
v___x_762_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6);
v___x_763_ = l_Lean_mkAppB(v___x_761_, v___x_762_, v_expr_756_);
v___x_764_ = l_Lean_Meta_Sym_shareCommonInc(v___x_763_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_775_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_775_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_775_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___f_769_; lean_object* v_boolExpr_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed), 16, 7);
lean_closure_set(v___f_769_, 0, v_sub_745_);
lean_closure_set(v___f_769_, 1, v_expr_756_);
lean_closure_set(v___f_769_, 2, v___x_757_);
lean_closure_set(v___f_769_, 3, v___x_758_);
lean_closure_set(v___f_769_, 4, v___x_759_);
lean_closure_set(v___f_769_, 5, v___x_760_);
lean_closure_set(v___f_769_, 6, v_subExpr_746_);
v_boolExpr_770_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_boolExpr_770_, 0, v_bvExpr_755_);
v___x_771_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_771_, 0, v_boolExpr_770_);
lean_ctor_set(v___x_771_, 1, v_origExpr_747_);
lean_ctor_set(v___x_771_, 2, v___f_769_);
lean_ctor_set(v___x_771_, 3, v_a_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_771_);
v___x_773_ = v___x_767_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_expr_756_);
lean_dec_ref(v_bvExpr_755_);
lean_dec_ref(v_origExpr_747_);
lean_dec_ref(v_subExpr_746_);
lean_dec_ref(v_sub_745_);
v_a_776_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_764_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_764_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___boxed(lean_object* v_sub_784_, lean_object* v_subExpr_785_, lean_object* v_origExpr_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_sub_784_, v_subExpr_785_, v_origExpr_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
lean_dec(v_a_788_);
lean_dec_ref(v_a_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(lean_object* v_sub_795_, lean_object* v_subExpr_796_, lean_object* v_origExpr_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_sub_795_, v_subExpr_796_, v_origExpr_797_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___boxed(lean_object* v_sub_808_, lean_object* v_subExpr_809_, lean_object* v_origExpr_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(v_sub_808_, v_subExpr_809_, v_origExpr_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
lean_dec(v_a_818_);
lean_dec_ref(v_a_817_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(lean_object* v_fst_821_, lean_object* v_fproof_822_, lean_object* v_snd_823_, lean_object* v_sproof_824_, lean_object* v_thd_825_, lean_object* v_tproof_826_){
_start:
{
if (lean_obj_tag(v_fproof_822_) == 0)
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_snd_823_, v_sproof_824_, v_thd_825_, v_tproof_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v___x_828_; 
lean_dec_ref(v_fst_821_);
v___x_828_ = lean_box(0);
return v___x_828_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_838_; 
v_val_829_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_838_ == 0)
{
v___x_831_ = v___x_827_;
v_isShared_832_ = v_isSharedCheck_838_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_val_829_);
lean_dec(v___x_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_838_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_833_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_fst_821_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v_val_829_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_834_);
v___x_836_ = v___x_831_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_860_; 
lean_dec_ref(v_fst_821_);
v_val_839_ = lean_ctor_get(v_fproof_822_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_fproof_822_);
if (v_isSharedCheck_860_ == 0)
{
v___x_841_ = v_fproof_822_;
v_isShared_842_ = v_isSharedCheck_860_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_val_839_);
lean_dec(v_fproof_822_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_860_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; 
lean_inc_ref(v_thd_825_);
lean_inc_ref(v_snd_823_);
v___x_843_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_snd_823_, v_sproof_824_, v_thd_825_, v_tproof_826_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_844_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_snd_823_);
v___x_845_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_thd_825_);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_844_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v_val_839_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_847_);
v___x_849_ = v___x_841_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
else
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
lean_del_object(v___x_841_);
lean_dec_ref(v_thd_825_);
lean_dec_ref(v_snd_823_);
v_val_851_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_859_ == 0)
{
v___x_853_ = v___x_843_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v___x_843_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v_val_839_);
lean_ctor_set(v___x_855_, 1, v_val_851_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(lean_object* v_expr_862_, lean_object* v_expr_863_, lean_object* v_expr_864_, lean_object* v_discr_865_, lean_object* v_lhs_866_, lean_object* v_rhs_867_, lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_discrExpr_872_, lean_object* v_lhsExpr_873_, lean_object* v_rhsExpr_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_862_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_863_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_864_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_discr_865_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_lhs_866_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v___x_892_, 1);
v___x_894_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_rhs_867_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_925_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_925_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_925_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; 
lean_inc(v_a_889_);
lean_inc(v_a_887_);
lean_inc(v_a_885_);
v___x_899_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(v_a_885_, v_a_891_, v_a_887_, v_a_893_, v_a_889_, v_a_895_);
if (lean_obj_tag(v___x_899_) == 1)
{
lean_object* v_val_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_920_; 
v_val_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_920_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_920_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_val_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_920_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_snd_904_; lean_object* v_fst_905_; lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v_snd_904_ = lean_ctor_get(v_val_900_, 1);
lean_inc(v_snd_904_);
v_fst_905_ = lean_ctor_get(v_val_900_, 0);
lean_inc(v_fst_905_);
lean_dec(v_val_900_);
v_fst_906_ = lean_ctor_get(v_snd_904_, 0);
lean_inc(v_fst_906_);
v_snd_907_ = lean_ctor_get(v_snd_904_, 1);
lean_inc(v_snd_907_);
lean_dec(v_snd_904_);
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0));
v___x_909_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6));
v___x_910_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0));
v___x_911_ = l_Lean_Name_mkStr6(v___x_868_, v___x_869_, v___x_870_, v___x_908_, v___x_909_, v___x_910_);
v___x_912_ = l_Lean_mkConst(v___x_911_, v___x_871_);
v___x_913_ = l_Lean_mkApp9(v___x_912_, v_discrExpr_872_, v_lhsExpr_873_, v_rhsExpr_874_, v_a_885_, v_a_887_, v_a_889_, v_fst_905_, v_fst_906_, v_snd_907_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_913_);
v___x_915_ = v___x_902_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_913_);
v___x_915_ = v_reuseFailAlloc_919_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_915_);
v___x_917_ = v___x_897_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_923_; 
lean_dec(v___x_899_);
lean_dec(v_a_889_);
lean_dec(v_a_887_);
lean_dec(v_a_885_);
lean_dec_ref(v_rhsExpr_874_);
lean_dec_ref(v_lhsExpr_873_);
lean_dec_ref(v_discrExpr_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_868_);
v___x_921_ = lean_box(0);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_921_);
v___x_923_ = v___x_897_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_dec(v_a_893_);
lean_dec(v_a_891_);
lean_dec(v_a_889_);
lean_dec(v_a_887_);
lean_dec(v_a_885_);
lean_dec_ref(v_rhsExpr_874_);
lean_dec_ref(v_lhsExpr_873_);
lean_dec_ref(v_discrExpr_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_868_);
return v___x_894_;
}
}
else
{
lean_dec(v_a_891_);
lean_dec(v_a_889_);
lean_dec(v_a_887_);
lean_dec(v_a_885_);
lean_dec_ref(v_rhsExpr_874_);
lean_dec_ref(v_lhsExpr_873_);
lean_dec_ref(v_discrExpr_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_868_);
lean_dec_ref(v_rhs_867_);
return v___x_892_;
}
}
else
{
lean_dec(v_a_889_);
lean_dec(v_a_887_);
lean_dec(v_a_885_);
lean_dec_ref(v_rhsExpr_874_);
lean_dec_ref(v_lhsExpr_873_);
lean_dec_ref(v_discrExpr_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_868_);
lean_dec_ref(v_rhs_867_);
lean_dec_ref(v_lhs_866_);
return v___x_890_;
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_a_887_);
lean_dec(v_a_885_);
lean_dec_ref(v_rhsExpr_874_);
lean_dec_ref(v_lhsExpr_873_);
lean_dec_ref(v_discrExpr_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_868_);
lean_dec_ref(v_rhs_867_);
lean_dec_ref(v_lhs_866_);
lean_dec_ref(v_discr_865_);
v_a_926_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_888_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_888_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec(v_a_885_);
lean_dec_ref(v_rhsExpr_874_);
lean_dec_ref(v_lhsExpr_873_);
lean_dec_ref(v_discrExpr_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_868_);
lean_dec_ref(v_rhs_867_);
lean_dec_ref(v_lhs_866_);
lean_dec_ref(v_discr_865_);
lean_dec_ref(v_expr_864_);
v_a_934_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_886_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_886_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec_ref(v_rhsExpr_874_);
lean_dec_ref(v_lhsExpr_873_);
lean_dec_ref(v_discrExpr_872_);
lean_dec(v___x_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_869_);
lean_dec_ref(v___x_868_);
lean_dec_ref(v_rhs_867_);
lean_dec_ref(v_lhs_866_);
lean_dec_ref(v_discr_865_);
lean_dec_ref(v_expr_864_);
lean_dec_ref(v_expr_863_);
v_a_942_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_884_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_884_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_950_ = _args[0];
lean_object* v_expr_951_ = _args[1];
lean_object* v_expr_952_ = _args[2];
lean_object* v_discr_953_ = _args[3];
lean_object* v_lhs_954_ = _args[4];
lean_object* v_rhs_955_ = _args[5];
lean_object* v___x_956_ = _args[6];
lean_object* v___x_957_ = _args[7];
lean_object* v___x_958_ = _args[8];
lean_object* v___x_959_ = _args[9];
lean_object* v_discrExpr_960_ = _args[10];
lean_object* v_lhsExpr_961_ = _args[11];
lean_object* v_rhsExpr_962_ = _args[12];
lean_object* v___y_963_ = _args[13];
lean_object* v___y_964_ = _args[14];
lean_object* v___y_965_ = _args[15];
lean_object* v___y_966_ = _args[16];
lean_object* v___y_967_ = _args[17];
lean_object* v___y_968_ = _args[18];
lean_object* v___y_969_ = _args[19];
lean_object* v___y_970_ = _args[20];
lean_object* v___y_971_ = _args[21];
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(v_expr_950_, v_expr_951_, v_expr_952_, v_discr_953_, v_lhs_954_, v_rhs_955_, v___x_956_, v___x_957_, v___x_958_, v___x_959_, v_discrExpr_960_, v_lhsExpr_961_, v_rhsExpr_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1));
v___x_982_ = l_Lean_mkConst(v___x_981_, v___x_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(lean_object* v_discr_983_, lean_object* v_lhs_984_, lean_object* v_rhs_985_, lean_object* v_discrExpr_986_, lean_object* v_lhsExpr_987_, lean_object* v_rhsExpr_988_, lean_object* v_origExpr_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_bvExpr_997_; lean_object* v_expr_998_; lean_object* v_bvExpr_999_; lean_object* v_expr_1000_; lean_object* v_bvExpr_1001_; lean_object* v_expr_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_bvExpr_997_ = lean_ctor_get(v_discr_983_, 0);
lean_inc_ref(v_bvExpr_997_);
v_expr_998_ = lean_ctor_get(v_discr_983_, 3);
lean_inc_ref_n(v_expr_998_, 2);
v_bvExpr_999_ = lean_ctor_get(v_lhs_984_, 0);
lean_inc_ref(v_bvExpr_999_);
v_expr_1000_ = lean_ctor_get(v_lhs_984_, 3);
lean_inc_ref_n(v_expr_1000_, 2);
v_bvExpr_1001_ = lean_ctor_get(v_rhs_985_, 0);
lean_inc_ref(v_bvExpr_1001_);
v_expr_1002_ = lean_ctor_get(v_rhs_985_, 3);
lean_inc_ref_n(v_expr_1002_, 2);
v___x_1003_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0));
v___x_1004_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1));
v___x_1005_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2));
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2);
v___x_1008_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__6);
v___x_1009_ = l_Lean_mkApp4(v___x_1007_, v___x_1008_, v_expr_998_, v_expr_1000_, v_expr_1002_);
v___x_1010_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1009_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1021_; 
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1021_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___f_1015_; lean_object* v_boolExpr_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___f_1015_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed), 22, 13);
lean_closure_set(v___f_1015_, 0, v_expr_998_);
lean_closure_set(v___f_1015_, 1, v_expr_1000_);
lean_closure_set(v___f_1015_, 2, v_expr_1002_);
lean_closure_set(v___f_1015_, 3, v_discr_983_);
lean_closure_set(v___f_1015_, 4, v_lhs_984_);
lean_closure_set(v___f_1015_, 5, v_rhs_985_);
lean_closure_set(v___f_1015_, 6, v___x_1003_);
lean_closure_set(v___f_1015_, 7, v___x_1004_);
lean_closure_set(v___f_1015_, 8, v___x_1005_);
lean_closure_set(v___f_1015_, 9, v___x_1006_);
lean_closure_set(v___f_1015_, 10, v_discrExpr_986_);
lean_closure_set(v___f_1015_, 11, v_lhsExpr_987_);
lean_closure_set(v___f_1015_, 12, v_rhsExpr_988_);
v_boolExpr_1016_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v_boolExpr_1016_, 0, v_bvExpr_997_);
lean_ctor_set(v_boolExpr_1016_, 1, v_bvExpr_999_);
lean_ctor_set(v_boolExpr_1016_, 2, v_bvExpr_1001_);
v___x_1017_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1017_, 0, v_boolExpr_1016_);
lean_ctor_set(v___x_1017_, 1, v_origExpr_989_);
lean_ctor_set(v___x_1017_, 2, v___f_1015_);
lean_ctor_set(v___x_1017_, 3, v_a_1011_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_dec_ref(v_expr_1002_);
lean_dec_ref(v_bvExpr_1001_);
lean_dec_ref(v_expr_1000_);
lean_dec_ref(v_bvExpr_999_);
lean_dec_ref(v_expr_998_);
lean_dec_ref(v_bvExpr_997_);
lean_dec_ref(v_origExpr_989_);
lean_dec_ref(v_rhsExpr_988_);
lean_dec_ref(v_lhsExpr_987_);
lean_dec_ref(v_discrExpr_986_);
lean_dec_ref(v_rhs_985_);
lean_dec_ref(v_lhs_984_);
lean_dec_ref(v_discr_983_);
v_a_1022_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1010_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1010_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___boxed(lean_object* v_discr_1030_, lean_object* v_lhs_1031_, lean_object* v_rhs_1032_, lean_object* v_discrExpr_1033_, lean_object* v_lhsExpr_1034_, lean_object* v_rhsExpr_1035_, lean_object* v_origExpr_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(v_discr_1030_, v_lhs_1031_, v_rhs_1032_, v_discrExpr_1033_, v_lhsExpr_1034_, v_rhsExpr_1035_, v_origExpr_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec_ref(v_a_1039_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(lean_object* v_discr_1045_, lean_object* v_lhs_1046_, lean_object* v_rhs_1047_, lean_object* v_discrExpr_1048_, lean_object* v_lhsExpr_1049_, lean_object* v_rhsExpr_1050_, lean_object* v_origExpr_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(v_discr_1045_, v_lhs_1046_, v_rhs_1047_, v_discrExpr_1048_, v_lhsExpr_1049_, v_rhsExpr_1050_, v_origExpr_1051_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___boxed(lean_object* v_discr_1062_, lean_object* v_lhs_1063_, lean_object* v_rhs_1064_, lean_object* v_discrExpr_1065_, lean_object* v_lhsExpr_1066_, lean_object* v_rhsExpr_1067_, lean_object* v_origExpr_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(v_discr_1062_, v_lhs_1063_, v_rhs_1064_, v_discrExpr_1065_, v_lhsExpr_1066_, v_rhsExpr_1067_, v_origExpr_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
return v_res_1078_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
}
#ifdef __cplusplus
}
#endif

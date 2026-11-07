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
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_gate___override(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_literal___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(uint8_t);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_not___override(lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_ite___override(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 146, 235, 19, 129, 87, 143, 4)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 10, 66, 130, 183, 180, 105, 128)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "not_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 196, 78, 204, 141, 145, 64, 13)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "cond_congr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 194, 82, 191, 111, 142, 125, 114)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "literal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 138, 65, 233, 49, 4, 83, 215)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object* v_expr_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
lean_dec_ref_known(v___x_66_, 1);
v___x_68_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__6);
v___x_69_ = l_Lean_mkAppB(v___x_68_, v_a_67_, v_expr_53_);
v___x_70_ = l_Lean_Meta_Sym_shareCommonInc(v___x_69_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
return v___x_70_;
}
else
{
lean_dec_ref(v_expr_53_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___boxed(lean_object* v_expr_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec_ref(v_a_77_);
lean_dec(v_a_76_);
lean_dec_ref(v_a_75_);
lean_dec(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(lean_object* v___x_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_85_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0___boxed(lean_object* v___x_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___lam__0(v___x_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
return v_res_112_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_box(0);
v___x_121_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__1));
v___x_122_ = l_Lean_mkConst(v___x_121_, v___x_120_);
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_129_ = lean_box(0);
v___x_130_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__5));
v___x_131_ = l_Lean_mkConst(v___x_130_, v___x_129_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
v___x_137_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__8));
v___x_138_ = l_Lean_mkConst(v___x_137_, v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(uint8_t v_val_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_boolExpr_147_; lean_object* v___x_148_; lean_object* v___y_150_; 
v_boolExpr_147_ = l_Std_Tactic_BVDecide_BVLogicalExpr_const___override(v_val_139_);
v___x_148_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__2);
if (v_val_139_ == 0)
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__6);
v___y_150_ = v___x_181_;
goto v___jp_149_;
}
else
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__9);
v___y_150_ = v___x_182_;
goto v___jp_149_;
}
v___jp_149_:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_inc_ref(v___y_150_);
v___x_151_ = l_Lean_Expr_app___override(v___x_148_, v___y_150_);
v___x_152_ = l_Lean_Meta_Sym_shareCommonInc(v___x_151_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_154_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v___x_152_, 1);
lean_inc_ref(v___y_150_);
v___x_154_ = l_Lean_Meta_Sym_shareCommonInc(v___y_150_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_164_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_164_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___f_159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___closed__3));
v___x_160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_160_, 0, v_boolExpr_147_);
lean_ctor_set(v___x_160_, 1, v_a_155_);
lean_ctor_set(v___x_160_, 2, v___f_159_);
lean_ctor_set(v___x_160_, 3, v_a_153_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_160_);
v___x_162_ = v___x_157_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_a_153_);
lean_dec_ref(v_boolExpr_147_);
v_a_165_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_154_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_154_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v_boolExpr_147_);
v_a_173_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_152_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_152_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg___boxed(lean_object* v_val_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
uint8_t v_val_boxed_191_; lean_object* v_res_192_; 
v_val_boxed_191_ = lean_unbox(v_val_183_);
v_res_192_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v_val_boxed_191_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_a_184_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(uint8_t v_val_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___redArg(v_val_193_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst___boxed(lean_object* v_val_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
uint8_t v_val_boxed_220_; lean_object* v_res_221_; 
v_val_boxed_220_ = lean_unbox(v_val_207_);
v_res_221_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkBoolConst(v_val_boxed_220_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(uint8_t v_gate_255_){
_start:
{
switch(v_gate_255_)
{
case 0:
{
lean_object* v___x_256_; 
v___x_256_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__2));
return v___x_256_;
}
case 1:
{
lean_object* v___x_257_; 
v___x_257_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__4));
return v___x_257_;
}
case 2:
{
lean_object* v___x_258_; 
v___x_258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__6));
return v___x_258_;
}
default: 
{
lean_object* v___x_259_; 
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__8));
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___boxed(lean_object* v_gate_260_){
_start:
{
uint8_t v_gate_boxed_261_; lean_object* v_res_262_; 
v_gate_boxed_261_ = lean_unbox(v_gate_260_);
v_res_262_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(v_gate_boxed_261_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(lean_object* v_fst_263_, lean_object* v_fproof_264_, lean_object* v_snd_265_, lean_object* v_sproof_266_){
_start:
{
if (lean_obj_tag(v_fproof_264_) == 0)
{
lean_dec_ref(v_snd_265_);
if (lean_obj_tag(v_sproof_266_) == 0)
{
lean_object* v___x_267_; 
lean_dec_ref(v_fst_263_);
v___x_267_ = lean_box(0);
return v___x_267_;
}
else
{
lean_object* v_val_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_277_; 
v_val_268_ = lean_ctor_get(v_sproof_266_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_sproof_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_270_ = v_sproof_266_;
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_val_268_);
lean_dec(v_sproof_266_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_277_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_fst_263_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_val_268_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 0, v___x_273_);
v___x_275_ = v___x_270_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_dec_ref(v_fst_263_);
if (lean_obj_tag(v_sproof_266_) == 0)
{
lean_object* v_val_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_287_; 
v_val_278_ = lean_ctor_get(v_fproof_264_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_fproof_264_);
if (v_isSharedCheck_287_ == 0)
{
v___x_280_ = v_fproof_264_;
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_val_278_);
lean_dec(v_fproof_264_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_282_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_snd_265_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_val_278_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_283_);
v___x_285_ = v___x_280_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
else
{
lean_object* v_val_288_; lean_object* v_val_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_snd_265_);
v_val_288_ = lean_ctor_get(v_fproof_264_, 0);
lean_inc(v_val_288_);
lean_dec_ref_known(v_fproof_264_, 1);
v_val_289_ = lean_ctor_get(v_sproof_266_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_sproof_266_);
if (v_isSharedCheck_297_ == 0)
{
v___x_291_ = v_sproof_266_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_val_289_);
lean_dec(v_sproof_266_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v_val_288_);
lean_ctor_set(v___x_293_, 1, v_val_289_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(lean_object* v_expr_298_, lean_object* v_expr_299_, lean_object* v_lhs_300_, lean_object* v_rhs_301_, lean_object* v_congrThm_302_, lean_object* v___x_303_, lean_object* v_lhsExpr_304_, lean_object* v_rhsExpr_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_298_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_318_) == 0)
{
lean_object* v_a_319_; lean_object* v___x_320_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_a_319_);
lean_dec_ref_known(v___x_318_, 1);
v___x_320_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_299_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_lhs_300_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v___x_322_, 1);
v___x_324_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_rhs_301_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_349_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_349_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_349_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_349_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_329_; 
lean_inc(v_a_321_);
lean_inc(v_a_319_);
v___x_329_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_a_319_, v_a_323_, v_a_321_, v_a_325_);
if (lean_obj_tag(v___x_329_) == 1)
{
lean_object* v_val_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_344_; 
v_val_330_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_344_ == 0)
{
v___x_332_ = v___x_329_;
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_val_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_344_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v_fst_334_; lean_object* v_snd_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v_fst_334_ = lean_ctor_get(v_val_330_, 0);
lean_inc(v_fst_334_);
v_snd_335_ = lean_ctor_get(v_val_330_, 1);
lean_inc(v_snd_335_);
lean_dec(v_val_330_);
v___x_336_ = l_Lean_mkConst(v_congrThm_302_, v___x_303_);
v___x_337_ = l_Lean_mkApp6(v___x_336_, v_lhsExpr_304_, v_rhsExpr_305_, v_a_319_, v_a_321_, v_fst_334_, v_snd_335_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 0, v___x_337_);
v___x_339_ = v___x_332_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_343_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_341_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_339_);
v___x_341_ = v___x_327_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_347_; 
lean_dec(v___x_329_);
lean_dec(v_a_321_);
lean_dec(v_a_319_);
lean_dec_ref(v_rhsExpr_305_);
lean_dec_ref(v_lhsExpr_304_);
lean_dec(v___x_303_);
lean_dec(v_congrThm_302_);
v___x_345_ = lean_box(0);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_345_);
v___x_347_ = v___x_327_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_dec(v_a_323_);
lean_dec(v_a_321_);
lean_dec(v_a_319_);
lean_dec_ref(v_rhsExpr_305_);
lean_dec_ref(v_lhsExpr_304_);
lean_dec(v___x_303_);
lean_dec(v_congrThm_302_);
return v___x_324_;
}
}
else
{
lean_dec(v_a_321_);
lean_dec(v_a_319_);
lean_dec_ref(v_rhsExpr_305_);
lean_dec_ref(v_lhsExpr_304_);
lean_dec(v___x_303_);
lean_dec(v_congrThm_302_);
lean_dec_ref(v_rhs_301_);
return v___x_322_;
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v_a_319_);
lean_dec_ref(v_rhsExpr_305_);
lean_dec_ref(v_lhsExpr_304_);
lean_dec(v___x_303_);
lean_dec(v_congrThm_302_);
lean_dec_ref(v_rhs_301_);
lean_dec_ref(v_lhs_300_);
v_a_350_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_320_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_320_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v_rhsExpr_305_);
lean_dec_ref(v_lhsExpr_304_);
lean_dec(v___x_303_);
lean_dec(v_congrThm_302_);
lean_dec_ref(v_rhs_301_);
lean_dec_ref(v_lhs_300_);
lean_dec_ref(v_expr_299_);
v_a_358_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_318_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_318_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_366_ = _args[0];
lean_object* v_expr_367_ = _args[1];
lean_object* v_lhs_368_ = _args[2];
lean_object* v_rhs_369_ = _args[3];
lean_object* v_congrThm_370_ = _args[4];
lean_object* v___x_371_ = _args[5];
lean_object* v_lhsExpr_372_ = _args[6];
lean_object* v_rhsExpr_373_ = _args[7];
lean_object* v___y_374_ = _args[8];
lean_object* v___y_375_ = _args[9];
lean_object* v___y_376_ = _args[10];
lean_object* v___y_377_ = _args[11];
lean_object* v___y_378_ = _args[12];
lean_object* v___y_379_ = _args[13];
lean_object* v___y_380_ = _args[14];
lean_object* v___y_381_ = _args[15];
lean_object* v___y_382_ = _args[16];
lean_object* v___y_383_ = _args[17];
lean_object* v___y_384_ = _args[18];
lean_object* v___y_385_ = _args[19];
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0(v_expr_366_, v_expr_367_, v_lhs_368_, v_rhs_369_, v_congrThm_370_, v___x_371_, v_lhsExpr_372_, v_rhsExpr_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_386_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_box(0);
v___x_395_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__1));
v___x_396_ = l_Lean_mkConst(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_box(0);
v___x_406_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__5));
v___x_407_ = l_Lean_mkConst(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_box(0);
v___x_416_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__8));
v___x_417_ = l_Lean_mkConst(v___x_416_, v___x_415_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_box(0);
v___x_426_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__11));
v___x_427_ = l_Lean_mkConst(v___x_426_, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_435_ = lean_box(0);
v___x_436_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__14));
v___x_437_ = l_Lean_mkConst(v___x_436_, v___x_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(lean_object* v_lhs_438_, lean_object* v_rhs_439_, lean_object* v_lhsExpr_440_, lean_object* v_rhsExpr_441_, uint8_t v_gate_442_, lean_object* v_origExpr_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_bvExpr_451_; lean_object* v_expr_452_; lean_object* v_bvExpr_453_; lean_object* v_expr_454_; lean_object* v_congrThm_455_; lean_object* v_boolExpr_456_; lean_object* v___x_457_; lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___y_461_; 
v_bvExpr_451_ = lean_ctor_get(v_lhs_438_, 0);
v_expr_452_ = lean_ctor_get(v_lhs_438_, 3);
lean_inc_ref_n(v_expr_452_, 2);
v_bvExpr_453_ = lean_ctor_get(v_rhs_439_, 0);
v_expr_454_ = lean_ctor_get(v_rhs_439_, 3);
lean_inc_ref_n(v_expr_454_, 2);
v_congrThm_455_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate(v_gate_442_);
lean_inc_ref(v_bvExpr_453_);
lean_inc_ref(v_bvExpr_451_);
v_boolExpr_456_ = l_Std_Tactic_BVDecide_BVLogicalExpr_gate___override(v_gate_442_, v_bvExpr_451_, v_bvExpr_453_);
v___x_457_ = lean_box(0);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___lam__0___boxed), 20, 8);
lean_closure_set(v___f_458_, 0, v_expr_452_);
lean_closure_set(v___f_458_, 1, v_expr_454_);
lean_closure_set(v___f_458_, 2, v_lhs_438_);
lean_closure_set(v___f_458_, 3, v_rhs_439_);
lean_closure_set(v___f_458_, 4, v_congrThm_455_);
lean_closure_set(v___f_458_, 5, v___x_457_);
lean_closure_set(v___f_458_, 6, v_lhsExpr_440_);
lean_closure_set(v___f_458_, 7, v_rhsExpr_441_);
v___x_459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__2);
switch(v_gate_442_)
{
case 0:
{
lean_object* v___x_481_; 
v___x_481_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__6);
v___y_461_ = v___x_481_;
goto v___jp_460_;
}
case 1:
{
lean_object* v___x_482_; 
v___x_482_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__9);
v___y_461_ = v___x_482_;
goto v___jp_460_;
}
case 2:
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__12);
v___y_461_ = v___x_483_;
goto v___jp_460_;
}
default: 
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___closed__15);
v___y_461_ = v___x_484_;
goto v___jp_460_;
}
}
v___jp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_inc_ref(v___y_461_);
v___x_462_ = l_Lean_mkApp3(v___x_459_, v___y_461_, v_expr_452_, v_expr_454_);
v___x_463_ = l_Lean_Meta_Sym_shareCommonInc(v___x_462_, v_a_444_, v_a_445_, v_a_446_, v_a_447_, v_a_448_, v_a_449_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_472_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_472_ == 0)
{
v___x_466_ = v___x_463_;
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_a_464_);
lean_dec(v___x_463_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_472_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_468_; lean_object* v___x_470_; 
v___x_468_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_468_, 0, v_boolExpr_456_);
lean_ctor_set(v___x_468_, 1, v_origExpr_443_);
lean_ctor_set(v___x_468_, 2, v___f_458_);
lean_ctor_set(v___x_468_, 3, v_a_464_);
if (v_isShared_467_ == 0)
{
lean_ctor_set(v___x_466_, 0, v___x_468_);
v___x_470_ = v___x_466_;
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
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec_ref(v___f_458_);
lean_dec_ref(v_boolExpr_456_);
lean_dec_ref(v_origExpr_443_);
v_a_473_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_463_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_463_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg___boxed(lean_object* v_lhs_485_, lean_object* v_rhs_486_, lean_object* v_lhsExpr_487_, lean_object* v_rhsExpr_488_, lean_object* v_gate_489_, lean_object* v_origExpr_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
uint8_t v_gate_boxed_498_; lean_object* v_res_499_; 
v_gate_boxed_498_ = lean_unbox(v_gate_489_);
v_res_499_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_lhs_485_, v_rhs_486_, v_lhsExpr_487_, v_rhsExpr_488_, v_gate_boxed_498_, v_origExpr_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(lean_object* v_lhs_500_, lean_object* v_rhs_501_, lean_object* v_lhsExpr_502_, lean_object* v_rhsExpr_503_, uint8_t v_gate_504_, lean_object* v_origExpr_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___redArg(v_lhs_500_, v_rhs_501_, v_lhsExpr_502_, v_rhsExpr_503_, v_gate_504_, v_origExpr_505_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate___boxed(lean_object** _args){
lean_object* v_lhs_519_ = _args[0];
lean_object* v_rhs_520_ = _args[1];
lean_object* v_lhsExpr_521_ = _args[2];
lean_object* v_rhsExpr_522_ = _args[3];
lean_object* v_gate_523_ = _args[4];
lean_object* v_origExpr_524_ = _args[5];
lean_object* v_a_525_ = _args[6];
lean_object* v_a_526_ = _args[7];
lean_object* v_a_527_ = _args[8];
lean_object* v_a_528_ = _args[9];
lean_object* v_a_529_ = _args[10];
lean_object* v_a_530_ = _args[11];
lean_object* v_a_531_ = _args[12];
lean_object* v_a_532_ = _args[13];
lean_object* v_a_533_ = _args[14];
lean_object* v_a_534_ = _args[15];
lean_object* v_a_535_ = _args[16];
lean_object* v_a_536_ = _args[17];
_start:
{
uint8_t v_gate_boxed_537_; lean_object* v_res_538_; 
v_gate_boxed_537_ = lean_unbox(v_gate_523_);
v_res_538_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate(v_lhs_519_, v_rhs_520_, v_lhsExpr_521_, v_rhsExpr_522_, v_gate_boxed_537_, v_origExpr_524_, v_a_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_a_525_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(lean_object* v_sub_540_, lean_object* v_expr_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v___x_544_, lean_object* v___x_545_, lean_object* v_subExpr_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_sub_540_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_599_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_599_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_599_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_599_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
if (lean_obj_tag(v_a_560_) == 1)
{
lean_object* v_val_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_594_; 
lean_del_object(v___x_562_);
v_val_564_ = lean_ctor_get(v_a_560_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v_a_560_);
if (v_isSharedCheck_594_ == 0)
{
v___x_566_ = v_a_560_;
v_isShared_567_ = v_isSharedCheck_594_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_val_564_);
lean_dec(v_a_560_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_594_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_541_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_585_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_585_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_585_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_585_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_573_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0));
v___x_574_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6));
v___x_575_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___closed__0));
v___x_576_ = l_Lean_Name_mkStr6(v___x_542_, v___x_543_, v___x_544_, v___x_573_, v___x_574_, v___x_575_);
v___x_577_ = l_Lean_mkConst(v___x_576_, v___x_545_);
v___x_578_ = l_Lean_mkApp3(v___x_577_, v_subExpr_546_, v_a_569_, v_val_564_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_578_);
v___x_580_ = v___x_566_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_584_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_580_);
v___x_582_ = v___x_571_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_del_object(v___x_566_);
lean_dec(v_val_564_);
lean_dec_ref(v_subExpr_546_);
lean_dec(v___x_545_);
lean_dec_ref(v___x_544_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_542_);
v_a_586_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_568_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_568_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_597_; 
lean_dec(v_a_560_);
lean_dec_ref(v_subExpr_546_);
lean_dec(v___x_545_);
lean_dec_ref(v___x_544_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v_expr_541_);
v___x_595_ = lean_box(0);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_595_);
v___x_597_ = v___x_562_;
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
}
else
{
lean_dec_ref(v_subExpr_546_);
lean_dec(v___x_545_);
lean_dec_ref(v___x_544_);
lean_dec_ref(v___x_543_);
lean_dec_ref(v___x_542_);
lean_dec_ref(v_expr_541_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_sub_600_ = _args[0];
lean_object* v_expr_601_ = _args[1];
lean_object* v___x_602_ = _args[2];
lean_object* v___x_603_ = _args[3];
lean_object* v___x_604_ = _args[4];
lean_object* v___x_605_ = _args[5];
lean_object* v_subExpr_606_ = _args[6];
lean_object* v___y_607_ = _args[7];
lean_object* v___y_608_ = _args[8];
lean_object* v___y_609_ = _args[9];
lean_object* v___y_610_ = _args[10];
lean_object* v___y_611_ = _args[11];
lean_object* v___y_612_ = _args[12];
lean_object* v___y_613_ = _args[13];
lean_object* v___y_614_ = _args[14];
lean_object* v___y_615_ = _args[15];
lean_object* v___y_616_ = _args[16];
lean_object* v___y_617_ = _args[17];
lean_object* v___y_618_ = _args[18];
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0(v_sub_600_, v_expr_601_, v___x_602_, v___x_603_, v___x_604_, v___x_605_, v_subExpr_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_619_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_box(0);
v___x_628_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__1));
v___x_629_ = l_Lean_mkConst(v___x_628_, v___x_627_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(lean_object* v_sub_630_, lean_object* v_subExpr_631_, lean_object* v_origExpr_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_bvExpr_640_; lean_object* v_expr_641_; lean_object* v_boolExpr_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___f_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_bvExpr_640_ = lean_ctor_get(v_sub_630_, 0);
v_expr_641_ = lean_ctor_get(v_sub_630_, 3);
lean_inc_ref_n(v_expr_641_, 2);
lean_inc_ref(v_bvExpr_640_);
v_boolExpr_642_ = l_Std_Tactic_BVDecide_BVLogicalExpr_not___override(v_bvExpr_640_);
v___x_643_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0));
v___x_644_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1));
v___x_645_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2));
v___x_646_ = lean_box(0);
v___f_647_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___lam__0___boxed), 19, 7);
lean_closure_set(v___f_647_, 0, v_sub_630_);
lean_closure_set(v___f_647_, 1, v_expr_641_);
lean_closure_set(v___f_647_, 2, v___x_643_);
lean_closure_set(v___f_647_, 3, v___x_644_);
lean_closure_set(v___f_647_, 4, v___x_645_);
lean_closure_set(v___f_647_, 5, v___x_646_);
lean_closure_set(v___f_647_, 6, v_subExpr_631_);
v___x_648_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___closed__2);
v___x_649_ = l_Lean_Expr_app___override(v___x_648_, v_expr_641_);
v___x_650_ = l_Lean_Meta_Sym_shareCommonInc(v___x_649_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_659_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_659_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_659_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_655_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_655_, 0, v_boolExpr_642_);
lean_ctor_set(v___x_655_, 1, v_origExpr_632_);
lean_ctor_set(v___x_655_, 2, v___f_647_);
lean_ctor_set(v___x_655_, 3, v_a_651_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v___x_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v___f_647_);
lean_dec_ref(v_boolExpr_642_);
lean_dec_ref(v_origExpr_632_);
v_a_660_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_650_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_650_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg___boxed(lean_object* v_sub_668_, lean_object* v_subExpr_669_, lean_object* v_origExpr_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_sub_668_, v_subExpr_669_, v_origExpr_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
lean_dec_ref(v_a_671_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(lean_object* v_sub_679_, lean_object* v_subExpr_680_, lean_object* v_origExpr_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___redArg(v_sub_679_, v_subExpr_680_, v_origExpr_681_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot___boxed(lean_object* v_sub_695_, lean_object* v_subExpr_696_, lean_object* v_origExpr_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkNot(v_sub_695_, v_subExpr_696_, v_origExpr_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(lean_object* v_fst_711_, lean_object* v_fproof_712_, lean_object* v_snd_713_, lean_object* v_sproof_714_, lean_object* v_thd_715_, lean_object* v_tproof_716_){
_start:
{
if (lean_obj_tag(v_fproof_712_) == 0)
{
lean_object* v___x_717_; 
v___x_717_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_snd_713_, v_sproof_714_, v_thd_715_, v_tproof_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v___x_718_; 
lean_dec_ref(v_fst_711_);
v___x_718_ = lean_box(0);
return v___x_718_;
}
else
{
lean_object* v_val_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_728_; 
v_val_719_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_728_ == 0)
{
v___x_721_ = v___x_717_;
v_isShared_722_ = v_isSharedCheck_728_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_val_719_);
lean_dec(v___x_717_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_728_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_723_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_fst_711_);
v___x_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
lean_ctor_set(v___x_724_, 1, v_val_719_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_724_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
else
{
lean_object* v_val_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v_fst_711_);
v_val_729_ = lean_ctor_get(v_fproof_712_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v_fproof_712_);
if (v_isSharedCheck_750_ == 0)
{
v___x_731_ = v_fproof_712_;
v_isShared_732_ = v_isSharedCheck_750_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_val_729_);
lean_dec(v_fproof_712_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_750_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; 
lean_inc_ref(v_thd_715_);
lean_inc_ref(v_snd_713_);
v___x_733_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_spec__0(v_snd_713_, v_sproof_714_, v_thd_715_, v_tproof_716_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_734_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_snd_713_);
v___x_735_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_thd_715_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_val_729_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_737_);
v___x_739_ = v___x_731_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
else
{
lean_object* v_val_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
lean_del_object(v___x_731_);
lean_dec_ref(v_thd_715_);
lean_dec_ref(v_snd_713_);
v_val_741_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v___x_733_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_val_741_);
lean_dec(v___x_733_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_val_729_);
lean_ctor_set(v___x_745_, 1, v_val_741_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(lean_object* v_expr_752_, lean_object* v_expr_753_, lean_object* v_expr_754_, lean_object* v_discr_755_, lean_object* v_lhs_756_, lean_object* v_rhs_757_, lean_object* v___x_758_, lean_object* v___x_759_, lean_object* v___x_760_, lean_object* v___x_761_, lean_object* v_discrExpr_762_, lean_object* v_lhsExpr_763_, lean_object* v_rhsExpr_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_752_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_779_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v___x_779_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_753_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_754_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_discr_755_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_lhs_756_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_rhs_757_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_818_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_787_);
if (v_isSharedCheck_818_ == 0)
{
v___x_790_ = v___x_787_;
v_isShared_791_ = v_isSharedCheck_818_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_a_788_);
lean_dec(v___x_787_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_818_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; 
lean_inc(v_a_782_);
lean_inc(v_a_780_);
lean_inc(v_a_778_);
v___x_792_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyTernaryProof___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte_spec__0(v_a_778_, v_a_784_, v_a_780_, v_a_786_, v_a_782_, v_a_788_);
if (lean_obj_tag(v___x_792_) == 1)
{
lean_object* v_val_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_813_; 
v_val_793_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_813_ == 0)
{
v___x_795_ = v___x_792_;
v_isShared_796_ = v_isSharedCheck_813_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_val_793_);
lean_dec(v___x_792_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_813_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v_snd_797_; lean_object* v_fst_798_; lean_object* v_fst_799_; lean_object* v_snd_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_808_; 
v_snd_797_ = lean_ctor_get(v_val_793_, 1);
lean_inc(v_snd_797_);
v_fst_798_ = lean_ctor_get(v_val_793_, 0);
lean_inc(v_fst_798_);
lean_dec(v_val_793_);
v_fst_799_ = lean_ctor_get(v_snd_797_, 0);
lean_inc(v_fst_799_);
v_snd_800_ = lean_ctor_get(v_snd_797_, 1);
lean_inc(v_snd_800_);
lean_dec(v_snd_797_);
v___x_801_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical_0__Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkGate_congrThmOfGate___closed__0));
v___x_802_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl___closed__6));
v___x_803_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___closed__0));
v___x_804_ = l_Lean_Name_mkStr6(v___x_758_, v___x_759_, v___x_760_, v___x_801_, v___x_802_, v___x_803_);
v___x_805_ = l_Lean_mkConst(v___x_804_, v___x_761_);
v___x_806_ = l_Lean_mkApp9(v___x_805_, v_discrExpr_762_, v_lhsExpr_763_, v_rhsExpr_764_, v_a_778_, v_a_780_, v_a_782_, v_fst_798_, v_fst_799_, v_snd_800_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_806_);
v___x_808_ = v___x_795_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_806_);
v___x_808_ = v_reuseFailAlloc_812_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_808_);
v___x_810_ = v___x_790_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_808_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec(v___x_792_);
lean_dec(v_a_782_);
lean_dec(v_a_780_);
lean_dec(v_a_778_);
lean_dec_ref(v_rhsExpr_764_);
lean_dec_ref(v_lhsExpr_763_);
lean_dec_ref(v_discrExpr_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
v___x_814_ = lean_box(0);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_814_);
v___x_816_ = v___x_790_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_dec(v_a_786_);
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_dec(v_a_780_);
lean_dec(v_a_778_);
lean_dec_ref(v_rhsExpr_764_);
lean_dec_ref(v_lhsExpr_763_);
lean_dec_ref(v_discrExpr_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
return v___x_787_;
}
}
else
{
lean_dec(v_a_784_);
lean_dec(v_a_782_);
lean_dec(v_a_780_);
lean_dec(v_a_778_);
lean_dec_ref(v_rhsExpr_764_);
lean_dec_ref(v_lhsExpr_763_);
lean_dec_ref(v_discrExpr_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v_rhs_757_);
return v___x_785_;
}
}
else
{
lean_dec(v_a_782_);
lean_dec(v_a_780_);
lean_dec(v_a_778_);
lean_dec_ref(v_rhsExpr_764_);
lean_dec_ref(v_lhsExpr_763_);
lean_dec_ref(v_discrExpr_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v_rhs_757_);
lean_dec_ref(v_lhs_756_);
return v___x_783_;
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_a_780_);
lean_dec(v_a_778_);
lean_dec_ref(v_rhsExpr_764_);
lean_dec_ref(v_lhsExpr_763_);
lean_dec_ref(v_discrExpr_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v_rhs_757_);
lean_dec_ref(v_lhs_756_);
lean_dec_ref(v_discr_755_);
v_a_819_ = lean_ctor_get(v___x_781_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_781_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_781_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_778_);
lean_dec_ref(v_rhsExpr_764_);
lean_dec_ref(v_lhsExpr_763_);
lean_dec_ref(v_discrExpr_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v_rhs_757_);
lean_dec_ref(v_lhs_756_);
lean_dec_ref(v_discr_755_);
lean_dec_ref(v_expr_754_);
v_a_827_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_779_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_779_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_rhsExpr_764_);
lean_dec_ref(v_lhsExpr_763_);
lean_dec_ref(v_discrExpr_762_);
lean_dec(v___x_761_);
lean_dec_ref(v___x_760_);
lean_dec_ref(v___x_759_);
lean_dec_ref(v___x_758_);
lean_dec_ref(v_rhs_757_);
lean_dec_ref(v_lhs_756_);
lean_dec_ref(v_discr_755_);
lean_dec_ref(v_expr_754_);
lean_dec_ref(v_expr_753_);
v_a_835_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_777_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_777_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_expr_843_ = _args[0];
lean_object* v_expr_844_ = _args[1];
lean_object* v_expr_845_ = _args[2];
lean_object* v_discr_846_ = _args[3];
lean_object* v_lhs_847_ = _args[4];
lean_object* v_rhs_848_ = _args[5];
lean_object* v___x_849_ = _args[6];
lean_object* v___x_850_ = _args[7];
lean_object* v___x_851_ = _args[8];
lean_object* v___x_852_ = _args[9];
lean_object* v_discrExpr_853_ = _args[10];
lean_object* v_lhsExpr_854_ = _args[11];
lean_object* v_rhsExpr_855_ = _args[12];
lean_object* v___y_856_ = _args[13];
lean_object* v___y_857_ = _args[14];
lean_object* v___y_858_ = _args[15];
lean_object* v___y_859_ = _args[16];
lean_object* v___y_860_ = _args[17];
lean_object* v___y_861_ = _args[18];
lean_object* v___y_862_ = _args[19];
lean_object* v___y_863_ = _args[20];
lean_object* v___y_864_ = _args[21];
lean_object* v___y_865_ = _args[22];
lean_object* v___y_866_ = _args[23];
lean_object* v___y_867_ = _args[24];
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0(v_expr_843_, v_expr_844_, v_expr_845_, v_discr_846_, v_lhs_847_, v_rhs_848_, v___x_849_, v___x_850_, v___x_851_, v___x_852_, v_discrExpr_853_, v_lhsExpr_854_, v_rhsExpr_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_868_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_876_ = lean_box(0);
v___x_877_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__1));
v___x_878_ = l_Lean_mkConst(v___x_877_, v___x_876_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(lean_object* v_discr_879_, lean_object* v_lhs_880_, lean_object* v_rhs_881_, lean_object* v_discrExpr_882_, lean_object* v_lhsExpr_883_, lean_object* v_rhsExpr_884_, lean_object* v_origExpr_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_bvExpr_893_; lean_object* v_expr_894_; lean_object* v_bvExpr_895_; lean_object* v_expr_896_; lean_object* v_bvExpr_897_; lean_object* v_expr_898_; lean_object* v_boolExpr_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v_bvExpr_893_ = lean_ctor_get(v_discr_879_, 0);
v_expr_894_ = lean_ctor_get(v_discr_879_, 3);
lean_inc_ref_n(v_expr_894_, 2);
v_bvExpr_895_ = lean_ctor_get(v_lhs_880_, 0);
v_expr_896_ = lean_ctor_get(v_lhs_880_, 3);
lean_inc_ref_n(v_expr_896_, 2);
v_bvExpr_897_ = lean_ctor_get(v_rhs_881_, 0);
v_expr_898_ = lean_ctor_get(v_rhs_881_, 3);
lean_inc_ref_n(v_expr_898_, 2);
lean_inc_ref(v_bvExpr_897_);
lean_inc_ref(v_bvExpr_895_);
lean_inc_ref(v_bvExpr_893_);
v_boolExpr_899_ = l_Std_Tactic_BVDecide_BVLogicalExpr_ite___override(v_bvExpr_893_, v_bvExpr_895_, v_bvExpr_897_);
v___x_900_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__0));
v___x_901_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__1));
v___x_902_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr___closed__2));
v___x_903_ = lean_box(0);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___lam__0___boxed), 25, 13);
lean_closure_set(v___f_904_, 0, v_expr_894_);
lean_closure_set(v___f_904_, 1, v_expr_896_);
lean_closure_set(v___f_904_, 2, v_expr_898_);
lean_closure_set(v___f_904_, 3, v_discr_879_);
lean_closure_set(v___f_904_, 4, v_lhs_880_);
lean_closure_set(v___f_904_, 5, v_rhs_881_);
lean_closure_set(v___f_904_, 6, v___x_900_);
lean_closure_set(v___f_904_, 7, v___x_901_);
lean_closure_set(v___f_904_, 8, v___x_902_);
lean_closure_set(v___f_904_, 9, v___x_903_);
lean_closure_set(v___f_904_, 10, v_discrExpr_882_);
lean_closure_set(v___f_904_, 11, v_lhsExpr_883_);
lean_closure_set(v___f_904_, 12, v_rhsExpr_884_);
v___x_905_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___closed__2);
v___x_906_ = l_Lean_mkApp3(v___x_905_, v_expr_894_, v_expr_896_, v_expr_898_);
v___x_907_ = l_Lean_Meta_Sym_shareCommonInc(v___x_906_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_916_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_912_, 0, v_boolExpr_899_);
lean_ctor_set(v___x_912_, 1, v_origExpr_885_);
lean_ctor_set(v___x_912_, 2, v___f_904_);
lean_ctor_set(v___x_912_, 3, v_a_908_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 0, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v___f_904_);
lean_dec_ref(v_boolExpr_899_);
lean_dec_ref(v_origExpr_885_);
v_a_917_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_907_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_907_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg___boxed(lean_object* v_discr_925_, lean_object* v_lhs_926_, lean_object* v_rhs_927_, lean_object* v_discrExpr_928_, lean_object* v_lhsExpr_929_, lean_object* v_rhsExpr_930_, lean_object* v_origExpr_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(v_discr_925_, v_lhs_926_, v_rhs_927_, v_discrExpr_928_, v_lhsExpr_929_, v_rhsExpr_930_, v_origExpr_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(lean_object* v_discr_940_, lean_object* v_lhs_941_, lean_object* v_rhs_942_, lean_object* v_discrExpr_943_, lean_object* v_lhsExpr_944_, lean_object* v_rhsExpr_945_, lean_object* v_origExpr_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___redArg(v_discr_940_, v_lhs_941_, v_rhs_942_, v_discrExpr_943_, v_lhsExpr_944_, v_rhsExpr_945_, v_origExpr_946_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte___boxed(lean_object** _args){
lean_object* v_discr_960_ = _args[0];
lean_object* v_lhs_961_ = _args[1];
lean_object* v_rhs_962_ = _args[2];
lean_object* v_discrExpr_963_ = _args[3];
lean_object* v_lhsExpr_964_ = _args[4];
lean_object* v_rhsExpr_965_ = _args[5];
lean_object* v_origExpr_966_ = _args[6];
lean_object* v_a_967_ = _args[7];
lean_object* v_a_968_ = _args[8];
lean_object* v_a_969_ = _args[9];
lean_object* v_a_970_ = _args[10];
lean_object* v_a_971_ = _args[11];
lean_object* v_a_972_ = _args[12];
lean_object* v_a_973_ = _args[13];
lean_object* v_a_974_ = _args[14];
lean_object* v_a_975_ = _args[15];
lean_object* v_a_976_ = _args[16];
lean_object* v_a_977_ = _args[17];
lean_object* v_a_978_ = _args[18];
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkIte(v_discr_960_, v_lhs_961_, v_rhs_962_, v_discrExpr_963_, v_lhsExpr_964_, v_rhsExpr_965_, v_origExpr_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
lean_dec(v_a_973_);
lean_dec_ref(v_a_972_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec(v_a_968_);
lean_dec_ref(v_a_967_);
return v_res_979_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_box(0);
v___x_988_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__1));
v___x_989_ = l_Lean_mkConst(v___x_988_, v___x_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(lean_object* v_bvPred_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_bvPred_998_; lean_object* v_originalExpr_999_; lean_object* v_expr_1000_; lean_object* v_boolExpr_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v_bvPred_998_ = lean_ctor_get(v_bvPred_990_, 0);
v_originalExpr_999_ = lean_ctor_get(v_bvPred_990_, 1);
lean_inc_ref(v_originalExpr_999_);
v_expr_1000_ = lean_ctor_get(v_bvPred_990_, 3);
lean_inc_ref(v_bvPred_998_);
v_boolExpr_1001_ = l_Std_Tactic_BVDecide_BVLogicalExpr_literal___override(v_bvPred_998_);
v___x_1002_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___closed__2);
lean_inc_ref(v_expr_1000_);
v___x_1003_ = l_Lean_Expr_app___override(v___x_1002_, v_expr_1000_);
v___x_1004_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1003_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1014_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1014_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed), 13, 1);
lean_closure_set(v___x_1009_, 0, v_bvPred_990_);
v___x_1010_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1010_, 0, v_boolExpr_1001_);
lean_ctor_set(v___x_1010_, 1, v_originalExpr_999_);
lean_ctor_set(v___x_1010_, 2, v___x_1009_);
lean_ctor_set(v___x_1010_, 3, v_a_1005_);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref(v_boolExpr_1001_);
lean_dec_ref(v_originalExpr_999_);
lean_dec_ref(v_bvPred_990_);
v_a_1015_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1004_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1004_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg___boxed(lean_object* v_bvPred_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_bvPred_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(lean_object* v_bvPred_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___redArg(v_bvPred_1032_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred___boxed(lean_object* v_bvPred_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_ofPred(v_bvPred_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
return v_res_1059_;
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

// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVExpr
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Basic public import Std.Tactic.BVDecide.Reflect import Lean.Meta.LitValues import Lean.Meta.Sym.LitValues import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(60, 36, 220, 177, 21, 103, 161, 68)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 213, 79, 77, 131, 135, 136, 165)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___lam__0___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object* v_w_15_, lean_object* v_expr_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_a_30_);
lean_dec_ref_known(v___x_29_, 1);
v___x_31_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6);
v___x_32_ = l_Lean_mkNatLit(v_w_15_);
v___x_33_ = l_Lean_mkApp3(v___x_31_, v___x_32_, v_a_30_, v_expr_16_);
v___x_34_ = l_Lean_Meta_Sym_shareCommonInc(v___x_33_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
return v___x_34_;
}
else
{
lean_dec_ref(v_expr_16_);
lean_dec(v_w_15_);
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___boxed(lean_object* v_w_35_, lean_object* v_expr_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_w_35_, v_expr_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
return v_res_49_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(1u);
v___x_56_ = l_Lean_Level_ofNat(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3);
v___x_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
lean_ctor_set(v___x_59_, 1, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4);
v___x_61_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2));
v___x_62_ = l_Lean_mkConst(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_box(0);
v___x_67_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_68_ = l_Lean_mkConst(v___x_67_, v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(lean_object* v_w_69_, lean_object* v_expr_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_71_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5);
v___x_72_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8);
v___x_73_ = l_Lean_mkNatLit(v_w_69_);
v___x_74_ = l_Lean_Expr_app___override(v___x_72_, v___x_73_);
v___x_75_ = l_Lean_mkAppB(v___x_71_, v___x_74_, v_expr_70_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object* v_ty_79_, lean_object* v_expr_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_ty_79_, v_a_81_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_119_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_119_ == 0)
{
v___x_89_ = v___x_86_;
v_isShared_90_ = v_isSharedCheck_119_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_119_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_91_ = l_Lean_Expr_cleanupAnnotations(v_a_87_);
v___x_92_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1));
v___x_93_ = l_Lean_Expr_isConstOf(v___x_91_, v___x_92_);
if (v___x_93_ == 0)
{
uint8_t v___x_94_; 
v___x_94_ = l_Lean_Expr_isApp(v___x_91_);
if (v___x_94_ == 0)
{
lean_dec_ref(v___x_91_);
lean_del_object(v___x_89_);
lean_dec_ref(v_expr_80_);
goto v___jp_83_;
}
else
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v___x_95_ = l_Lean_Expr_appFnCleanup___redArg(v___x_91_);
v___x_96_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_97_ = l_Lean_Expr_isConstOf(v___x_95_, v___x_96_);
lean_dec_ref(v___x_95_);
if (v___x_97_ == 0)
{
lean_del_object(v___x_89_);
lean_dec_ref(v_expr_80_);
goto v___jp_83_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_expr_80_);
if (lean_obj_tag(v___x_98_) == 1)
{
lean_object* v_val_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_110_; 
v_val_99_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_110_ == 0)
{
v___x_101_ = v___x_98_;
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_val_99_);
lean_dec(v___x_98_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_110_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_val_103_; lean_object* v___x_105_; 
v_val_103_ = lean_ctor_get(v_val_99_, 1);
lean_inc(v_val_103_);
lean_dec(v_val_99_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v_val_103_);
v___x_105_ = v___x_101_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_val_103_);
v___x_105_ = v_reuseFailAlloc_109_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_107_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_105_);
v___x_107_ = v___x_89_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
else
{
lean_object* v___x_111_; lean_object* v___x_113_; 
lean_dec(v___x_98_);
v___x_111_ = lean_box(0);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_111_);
v___x_113_ = v___x_89_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
else
{
lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec_ref(v___x_91_);
v___x_115_ = l_Lean_Meta_Sym_getNatValue_x3f(v_expr_80_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_115_);
v___x_117_ = v___x_89_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
lean_dec_ref(v_expr_80_);
v_a_120_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_86_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_86_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
v___jp_83_:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_box(0);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___boxed(lean_object* v_ty_128_, lean_object* v_expr_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_ty_128_, v_expr_129_, v_a_130_);
lean_dec(v_a_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(lean_object* v_ty_133_, lean_object* v_expr_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_ty_133_, v_expr_134_, v_a_143_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___boxed(lean_object* v_ty_148_, lean_object* v_expr_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(v_ty_148_, v_expr_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___lam__0(lean_object* v___x_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_163_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___lam__0___boxed(lean_object* v___x_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___lam__0(v___x_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
return v_res_190_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_box(0);
v___x_199_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1));
v___x_200_ = l_Lean_mkConst(v___x_199_, v___x_198_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_box(0);
v___x_206_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4));
v___x_207_ = l_Lean_Expr_const___override(v___x_206_, v___x_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(lean_object* v_w_210_, lean_object* v_val_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_bvExpr_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_inc(v_val_211_);
lean_inc_n(v_w_210_, 2);
v_bvExpr_219_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_210_, v_val_211_);
v___x_220_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2);
v___x_221_ = l_Lean_mkNatLit(v_w_210_);
v___x_222_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5);
v___x_223_ = l_Lean_mkNatLit(v_val_211_);
lean_inc_ref(v___x_221_);
v___x_224_ = l_Lean_mkAppB(v___x_222_, v___x_221_, v___x_223_);
lean_inc_ref(v___x_224_);
v___x_225_ = l_Lean_mkAppB(v___x_220_, v___x_221_, v___x_224_);
v___x_226_ = l_Lean_Meta_Sym_shareCommonInc(v___x_225_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_Meta_Sym_shareCommonInc(v___x_224_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_238_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_238_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___f_233_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__6));
v___x_234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_234_, 0, v_w_210_);
lean_ctor_set(v___x_234_, 1, v_bvExpr_219_);
lean_ctor_set(v___x_234_, 2, v_a_229_);
lean_ctor_set(v___x_234_, 3, v___f_233_);
lean_ctor_set(v___x_234_, 4, v_a_227_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
lean_dec(v_a_227_);
lean_dec_ref(v_bvExpr_219_);
lean_dec(v_w_210_);
v_a_239_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_228_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_228_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
lean_dec_ref(v___x_224_);
lean_dec_ref(v_bvExpr_219_);
lean_dec(v_w_210_);
v_a_247_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_226_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_226_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___boxed(lean_object* v_w_255_, lean_object* v_val_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_w_255_, v_val_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(lean_object* v_w_265_, lean_object* v_val_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_w_265_, v_val_266_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___boxed(lean_object* v_w_280_, lean_object* v_val_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(v_w_280_, v_val_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
lean_dec(v_a_288_);
lean_dec_ref(v_a_287_);
lean_dec(v_a_286_);
lean_dec_ref(v_a_285_);
lean_dec(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_294_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVExpr(builtin);
}
#ifdef __cplusplus
}
#endif

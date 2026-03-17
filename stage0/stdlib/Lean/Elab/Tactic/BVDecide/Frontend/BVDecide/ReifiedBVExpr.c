// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.ReifiedBVExpr
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reflect public import Std.Tactic.BVDecide.Reflect import Lean.Meta.LitValues
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_getBitVecValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVExpr"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__4_value),LEAN_SCALAR_PTR_LITERAL(60, 36, 220, 177, 21, 103, 161, 68)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 7, 174, 153, 9, 234, 93, 144)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___lam__0___boxed, .m_arity = 7, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 213, 79, 77, 131, 135, 136, 165)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(lean_object* v_w_15_, lean_object* v_expr_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_34_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_34_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_34_ == 0)
{
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_a_24_);
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_34_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v___x_28_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___closed__6);
v___x_29_ = l_Lean_mkNatLit(v_w_15_);
v___x_30_ = l_Lean_mkApp3(v___x_28_, v___x_29_, v_a_24_, v_expr_16_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_30_);
v___x_32_ = v___x_26_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
else
{
lean_dec_ref(v_expr_16_);
lean_dec(v_w_15_);
return v___x_23_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr___boxed(lean_object* v_w_35_, lean_object* v_expr_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkEvalExpr(v_w_35_, v_expr_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
lean_dec(v_a_37_);
return v_res_43_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__3(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = l_Lean_Level_ofNat(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__4(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__3);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__4, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__4_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__4);
v___x_55_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__2));
v___x_56_ = l_Lean_mkConst(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__8(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_62_ = l_Lean_mkConst(v___x_61_, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl(lean_object* v_w_63_, lean_object* v_expr_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__5);
v___x_66_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__8);
v___x_67_ = l_Lean_mkNatLit(v_w_63_);
v___x_68_ = l_Lean_Expr_app___override(v___x_66_, v___x_67_);
v___x_69_ = l_Lean_mkAppB(v___x_65_, v___x_68_, v_expr_64_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___lam__0(lean_object* v___x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_70_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___lam__0___boxed(lean_object* v___x_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___lam__0(v___x_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__1));
v___x_95_ = l_Lean_mkConst(v___x_94_, v___x_93_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom(lean_object* v_e_98_, lean_object* v_width_99_, uint8_t v_synthetic_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; 
lean_inc(v_width_99_);
v___x_107_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_lookup(v_e_98_, v_width_99_, v_synthetic_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_122_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_122_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_122_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_122_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___f_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_112_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__2);
lean_inc(v_width_99_);
v___x_113_ = l_Lean_mkNatLit(v_width_99_);
lean_inc(v_a_108_);
v___x_114_ = l_Lean_mkNatLit(v_a_108_);
v___x_115_ = l_Lean_mkAppB(v___x_112_, v___x_113_, v___x_114_);
v___f_116_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__3));
lean_inc(v_width_99_);
v___x_117_ = l_Std_Tactic_BVDecide_BVExpr_var___override(v_width_99_, v_a_108_);
lean_inc_ref(v___x_115_);
v___x_118_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_118_, 0, v_width_99_);
lean_ctor_set(v___x_118_, 1, v___x_117_);
lean_ctor_set(v___x_118_, 2, v___x_115_);
lean_ctor_set(v___x_118_, 3, v___f_116_);
lean_ctor_set(v___x_118_, 4, v___x_115_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_118_);
v___x_120_ = v___x_110_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
lean_dec(v_width_99_);
v_a_123_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_107_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_107_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___boxed(lean_object* v_e_131_, lean_object* v_width_132_, lean_object* v_synthetic_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
uint8_t v_synthetic_boxed_140_; lean_object* v_res_141_; 
v_synthetic_boxed_140_ = lean_unbox(v_synthetic_133_);
v_res_141_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom(v_e_131_, v_width_132_, v_synthetic_boxed_140_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object* v_ty_145_, lean_object* v_expr_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_ty_145_, v_a_148_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_155_);
v___x_157_ = l_Lean_Expr_cleanupAnnotations(v_a_156_);
v___x_158_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1));
v___x_159_ = l_Lean_Expr_isConstOf(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_Expr_isApp(v___x_157_);
if (v___x_160_ == 0)
{
lean_dec_ref(v___x_157_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_expr_146_);
goto v___jp_152_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_157_);
v___x_162_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_163_ = l_Lean_Expr_isConstOf(v___x_161_, v___x_162_);
lean_dec_ref(v___x_161_);
if (v___x_163_ == 0)
{
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_expr_146_);
goto v___jp_152_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = l_Lean_Meta_getBitVecValue_x3f(v_expr_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_185_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_185_ == 0)
{
v___x_167_ = v___x_164_;
v_isShared_168_ = v_isSharedCheck_185_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_164_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_185_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
if (lean_obj_tag(v_a_165_) == 1)
{
lean_object* v_val_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_180_; 
v_val_169_ = lean_ctor_get(v_a_165_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_a_165_);
if (v_isSharedCheck_180_ == 0)
{
v___x_171_ = v_a_165_;
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_val_169_);
lean_dec(v_a_165_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_180_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v_snd_173_; lean_object* v___x_175_; 
v_snd_173_ = lean_ctor_get(v_val_169_, 1);
lean_inc(v_snd_173_);
lean_dec(v_val_169_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v_snd_173_);
v___x_175_ = v___x_171_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_snd_173_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_175_);
v___x_177_ = v___x_167_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec(v_a_165_);
v___x_181_ = lean_box(0);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_181_);
v___x_183_ = v___x_167_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
v_a_186_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_164_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_164_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
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
}
}
else
{
lean_object* v___x_194_; 
lean_dec_ref(v___x_157_);
v___x_194_ = l_Lean_Meta_getNatValue_x3f(v_expr_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec_ref(v_expr_146_);
return v___x_194_;
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec_ref(v_expr_146_);
v_a_195_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_155_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_155_);
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
v___jp_152_:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___boxed(lean_object* v_ty_203_, lean_object* v_expr_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_ty_203_, v_expr_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f(lean_object* v_ty_211_, lean_object* v_expr_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_ty_211_, v_expr_212_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f___boxed(lean_object* v_ty_220_, lean_object* v_expr_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_getNatOrBvValue_x3f(v_ty_220_, v_expr_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_222_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___redArg(lean_object* v_e_229_, lean_object* v___y_230_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Lean_Expr_hasMVar(v_e_229_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v_e_229_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v_mctx_235_; lean_object* v___x_236_; lean_object* v_fst_237_; lean_object* v_snd_238_; lean_object* v___x_239_; lean_object* v_cache_240_; lean_object* v_zetaDeltaFVarIds_241_; lean_object* v_postponed_242_; lean_object* v_diag_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_252_; 
v___x_234_ = lean_st_ref_get(v___y_230_);
v_mctx_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc_ref(v_mctx_235_);
lean_dec(v___x_234_);
v___x_236_ = l_Lean_instantiateMVarsCore(v_mctx_235_, v_e_229_);
v_fst_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_fst_237_);
v_snd_238_ = lean_ctor_get(v___x_236_, 1);
lean_inc(v_snd_238_);
lean_dec_ref(v___x_236_);
v___x_239_ = lean_st_ref_take(v___y_230_);
v_cache_240_ = lean_ctor_get(v___x_239_, 1);
v_zetaDeltaFVarIds_241_ = lean_ctor_get(v___x_239_, 2);
v_postponed_242_ = lean_ctor_get(v___x_239_, 3);
v_diag_243_ = lean_ctor_get(v___x_239_, 4);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_252_ == 0)
{
lean_object* v_unused_253_; 
v_unused_253_ = lean_ctor_get(v___x_239_, 0);
lean_dec(v_unused_253_);
v___x_245_ = v___x_239_;
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_diag_243_);
lean_inc(v_postponed_242_);
lean_inc(v_zetaDeltaFVarIds_241_);
lean_inc(v_cache_240_);
lean_dec(v___x_239_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_252_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___x_248_; 
if (v_isShared_246_ == 0)
{
lean_ctor_set(v___x_245_, 0, v_snd_238_);
v___x_248_ = v___x_245_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_snd_238_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_cache_240_);
lean_ctor_set(v_reuseFailAlloc_251_, 2, v_zetaDeltaFVarIds_241_);
lean_ctor_set(v_reuseFailAlloc_251_, 3, v_postponed_242_);
lean_ctor_set(v_reuseFailAlloc_251_, 4, v_diag_243_);
v___x_248_ = v_reuseFailAlloc_251_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_st_ref_set(v___y_230_, v___x_248_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v_fst_237_);
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___redArg___boxed(lean_object* v_e_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___redArg(v_e_254_, v___y_255_);
lean_dec(v___y_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0(lean_object* v_e_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___redArg(v_e_258_, v___y_261_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___boxed(lean_object* v_e_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0(v_e_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(lean_object* v_x_274_, uint8_t v_synthetic_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_282_; 
lean_inc(v_a_280_);
lean_inc_ref(v_a_279_);
lean_inc(v_a_278_);
lean_inc_ref(v_a_277_);
lean_inc_ref(v_x_274_);
v___x_282_ = lean_infer_type(v_x_274_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v___x_282_);
lean_inc(v_a_280_);
lean_inc_ref(v_a_279_);
lean_inc(v_a_278_);
lean_inc_ref(v_a_277_);
v___x_284_ = l_Lean_Meta_whnfR(v_a_283_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_345_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref(v___x_284_);
v___x_286_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom_spec__0___redArg(v_a_285_, v_a_278_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_345_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_345_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_345_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_296_ = l_Lean_Expr_cleanupAnnotations(v_a_287_);
v___x_297_ = l_Lean_Expr_isApp(v___x_296_);
if (v___x_297_ == 0)
{
lean_dec_ref(v___x_296_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_x_274_);
goto v___jp_291_;
}
else
{
lean_object* v_arg_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_arg_298_ = lean_ctor_get(v___x_296_, 1);
lean_inc_ref(v_arg_298_);
v___x_299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_296_);
v___x_300_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_301_ = l_Lean_Expr_isConstOf(v___x_299_, v___x_300_);
lean_dec_ref(v___x_299_);
if (v___x_301_ == 0)
{
lean_dec_ref(v_arg_298_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_x_274_);
goto v___jp_291_;
}
else
{
lean_object* v___x_302_; 
lean_del_object(v___x_289_);
lean_inc(v_a_280_);
lean_inc_ref(v_a_279_);
lean_inc(v_a_278_);
lean_inc_ref(v_a_277_);
v___x_302_ = l_Lean_Meta_getNatValue_x3f(v_arg_298_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec_ref(v_arg_298_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_336_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_336_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_336_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_336_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
if (lean_obj_tag(v_a_303_) == 1)
{
lean_object* v_val_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_331_; 
lean_del_object(v___x_305_);
v_val_307_ = lean_ctor_get(v_a_303_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_303_);
if (v_isSharedCheck_331_ == 0)
{
v___x_309_ = v_a_303_;
v_isShared_310_ = v_isSharedCheck_331_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_val_307_);
lean_dec(v_a_303_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_331_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom(v_x_274_, v_val_307_, v_synthetic_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_322_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_322_ == 0)
{
v___x_314_ = v___x_311_;
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_311_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v_a_312_);
v___x_317_ = v___x_309_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_321_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_330_; 
lean_del_object(v___x_309_);
v_a_323_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_330_ == 0)
{
v___x_325_ = v___x_311_;
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_311_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_330_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_334_; 
lean_dec(v_a_303_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_x_274_);
v___x_332_ = lean_box(0);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_332_);
v___x_334_ = v___x_305_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_x_274_);
v_a_337_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_302_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_302_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
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
}
v___jp_291_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
v___x_292_ = lean_box(0);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_292_);
v___x_294_ = v___x_289_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_x_274_);
v_a_346_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_284_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_284_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v_a_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_361_; 
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec(v_a_276_);
lean_dec_ref(v_x_274_);
v_a_354_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_361_ == 0)
{
v___x_356_ = v___x_282_;
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_a_354_);
lean_dec(v___x_282_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_361_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_359_; 
if (v_isShared_357_ == 0)
{
v___x_359_ = v___x_356_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_354_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom___boxed(lean_object* v_x_362_, lean_object* v_synthetic_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
uint8_t v_synthetic_boxed_370_; lean_object* v_res_371_; 
v_synthetic_boxed_370_ = lean_unbox(v_synthetic_363_);
v_res_371_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_bitVecAtom(v_x_362_, v_synthetic_boxed_370_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__2(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = lean_box(0);
v___x_380_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__1));
v___x_381_ = l_Lean_mkConst(v___x_380_, v___x_379_);
return v___x_381_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__5(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_386_ = lean_box(0);
v___x_387_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__4));
v___x_388_ = l_Lean_Expr_const___override(v___x_387_, v___x_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(lean_object* v_w_389_, lean_object* v_val_390_){
_start:
{
lean_object* v_bvExpr_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v_expr_398_; lean_object* v_proof_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_inc(v_val_390_);
lean_inc(v_w_389_);
v_bvExpr_392_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_389_, v_val_390_);
v___x_393_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__2);
lean_inc(v_w_389_);
v___x_394_ = l_Lean_mkNatLit(v_w_389_);
v___x_395_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___closed__5);
v___x_396_ = l_Lean_mkNatLit(v_val_390_);
lean_inc_ref(v___x_394_);
v___x_397_ = l_Lean_mkAppB(v___x_395_, v___x_394_, v___x_396_);
lean_inc_ref(v___x_397_);
v_expr_398_ = l_Lean_mkAppB(v___x_393_, v___x_394_, v___x_397_);
v_proof_399_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkAtom___closed__3));
v___x_400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_400_, 0, v_w_389_);
lean_ctor_set(v___x_400_, 1, v_bvExpr_392_);
lean_ctor_set(v___x_400_, 2, v___x_397_);
lean_ctor_set(v___x_400_, 3, v_proof_399_);
lean_ctor_set(v___x_400_, 4, v_expr_398_);
v___x_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_401_, 0, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg___boxed(lean_object* v_w_402_, lean_object* v_val_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(v_w_402_, v_val_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst(lean_object* v_w_406_, lean_object* v_val_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___redArg(v_w_406_, v_val_407_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst___boxed(lean_object* v_w_415_, lean_object* v_val_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVExpr_mkBVConst(v_w_415_, v_val_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
lean_dec(v_a_417_);
return v_res_423_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
lean_object* initialize_Lean_Meta_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_ReifiedBVExpr(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 7, 174, 153, 9, 234, 93, 144)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(lean_object* v_w_15_, lean_object* v_expr_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_a_27_);
lean_dec_ref_known(v___x_26_, 1);
v___x_28_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___closed__6);
v___x_29_ = l_Lean_mkNatLit(v_w_15_);
v___x_30_ = l_Lean_mkApp3(v___x_28_, v___x_29_, v_a_27_, v_expr_16_);
v___x_31_ = l_Lean_Meta_Sym_shareCommonInc(v___x_30_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_);
return v___x_31_;
}
else
{
lean_dec_ref(v_expr_16_);
lean_dec(v_w_15_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr___boxed(lean_object* v_w_32_, lean_object* v_expr_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkEvalExpr(v_w_32_, v_expr_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_43_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(1u);
v___x_50_ = l_Lean_Level_ofNat(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__3);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__4);
v___x_55_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__2));
v___x_56_ = l_Lean_mkConst(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_62_ = l_Lean_mkConst(v___x_61_, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl(lean_object* v_w_63_, lean_object* v_expr_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_65_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__5);
v___x_66_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__8);
v___x_67_ = l_Lean_mkNatLit(v_w_63_);
v___x_68_ = l_Lean_Expr_app___override(v___x_66_, v___x_67_);
v___x_69_ = l_Lean_mkAppB(v___x_65_, v___x_68_, v_expr_64_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0(lean_object* v___x_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_70_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0___boxed(lean_object* v___x_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___lam__0(v___x_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_, v___y_89_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_91_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_box(0);
v___x_100_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__1));
v___x_101_ = l_Lean_mkConst(v___x_100_, v___x_99_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(lean_object* v_e_104_, lean_object* v_width_105_, uint8_t v_synthetic_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
lean_inc(v_width_105_);
v___x_116_ = l_Lean_Meta_Tactic_BVDecide_M_lookup(v_e_104_, v_width_105_, v_synthetic_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc_n(v_a_117_, 2);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__2);
lean_inc(v_width_105_);
v___x_119_ = l_Lean_mkNatLit(v_width_105_);
v___x_120_ = l_Lean_mkNatLit(v_a_117_);
v___x_121_ = l_Lean_mkAppB(v___x_118_, v___x_119_, v___x_120_);
v___x_122_ = l_Lean_Meta_Sym_shareCommonInc(v___x_121_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_133_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_133_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___f_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___f_127_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3));
lean_inc(v_width_105_);
v___x_128_ = l_Std_Tactic_BVDecide_BVExpr_var___override(v_width_105_, v_a_117_);
lean_inc(v_a_123_);
v___x_129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_129_, 0, v_width_105_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
lean_ctor_set(v___x_129_, 2, v_a_123_);
lean_ctor_set(v___x_129_, 3, v___f_127_);
lean_ctor_set(v___x_129_, 4, v_a_123_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_129_);
v___x_131_ = v___x_125_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_a_117_);
lean_dec(v_width_105_);
v_a_134_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_122_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_122_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
lean_dec(v_width_105_);
v_a_142_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v___x_116_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v___x_116_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___boxed(lean_object* v_e_150_, lean_object* v_width_151_, lean_object* v_synthetic_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
uint8_t v_synthetic_boxed_162_; lean_object* v_res_163_; 
v_synthetic_boxed_162_ = lean_unbox(v_synthetic_152_);
v_res_163_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(v_e_150_, v_width_151_, v_synthetic_boxed_162_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(lean_object* v_ty_167_, lean_object* v_expr_168_, lean_object* v_a_169_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_ty_167_, v_a_169_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_207_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_207_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_207_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_207_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_179_ = l_Lean_Expr_cleanupAnnotations(v_a_175_);
v___x_180_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___closed__1));
v___x_181_ = l_Lean_Expr_isConstOf(v___x_179_, v___x_180_);
if (v___x_181_ == 0)
{
uint8_t v___x_182_; 
v___x_182_ = l_Lean_Expr_isApp(v___x_179_);
if (v___x_182_ == 0)
{
lean_dec_ref(v___x_179_);
lean_del_object(v___x_177_);
lean_dec_ref(v_expr_168_);
goto v___jp_171_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = l_Lean_Expr_appFnCleanup___redArg(v___x_179_);
v___x_184_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_185_ = l_Lean_Expr_isConstOf(v___x_183_, v___x_184_);
lean_dec_ref(v___x_183_);
if (v___x_185_ == 0)
{
lean_del_object(v___x_177_);
lean_dec_ref(v_expr_168_);
goto v___jp_171_;
}
else
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Sym_getBitVecValue_x3f(v_expr_168_);
if (lean_obj_tag(v___x_186_) == 1)
{
lean_object* v_val_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_198_; 
v_val_187_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_198_ == 0)
{
v___x_189_ = v___x_186_;
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_val_187_);
lean_dec(v___x_186_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_198_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_val_191_; lean_object* v___x_193_; 
v_val_191_ = lean_ctor_get(v_val_187_, 1);
lean_inc(v_val_191_);
lean_dec(v_val_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 0, v_val_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_val_191_);
v___x_193_ = v_reuseFailAlloc_197_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_195_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_193_);
v___x_195_ = v___x_177_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v___x_193_);
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
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_dec(v___x_186_);
v___x_199_ = lean_box(0);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_199_);
v___x_201_ = v___x_177_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
else
{
lean_object* v___x_203_; lean_object* v___x_205_; 
lean_dec_ref(v___x_179_);
v___x_203_ = l_Lean_Meta_Sym_getNatValue_x3f(v_expr_168_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_203_);
v___x_205_ = v___x_177_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_expr_168_);
v_a_208_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_174_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_174_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
v___jp_171_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_box(0);
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg___boxed(lean_object* v_ty_216_, lean_object* v_expr_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_ty_216_, v_expr_217_, v_a_218_);
lean_dec(v_a_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(lean_object* v_ty_221_, lean_object* v_expr_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___redArg(v_ty_221_, v_expr_222_, v_a_228_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f___boxed(lean_object* v_ty_233_, lean_object* v_expr_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_getNatOrBvValue_x3f(v_ty_233_, v_expr_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(lean_object* v_x_245_, uint8_t v_synthetic_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v___x_256_; 
lean_inc_ref(v_x_245_);
v___x_256_ = l_Lean_Meta_Sym_inferType(v_x_245_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_316_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_316_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_316_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_316_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Meta_Sym_instantiateMVarsS(v_a_257_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_307_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_307_ == 0)
{
v___x_264_ = v___x_261_;
v_isShared_265_ = v_isSharedCheck_307_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_307_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = l_Lean_Expr_cleanupAnnotations(v_a_262_);
v___x_272_ = l_Lean_Expr_isApp(v___x_271_);
if (v___x_272_ == 0)
{
lean_dec_ref(v___x_271_);
lean_del_object(v___x_259_);
lean_dec_ref(v_x_245_);
goto v___jp_266_;
}
else
{
lean_object* v_arg_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_arg_273_ = lean_ctor_get(v___x_271_, 1);
lean_inc_ref(v_arg_273_);
v___x_274_ = l_Lean_Expr_appFnCleanup___redArg(v___x_271_);
v___x_275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVRefl___closed__7));
v___x_276_ = l_Lean_Expr_isConstOf(v___x_274_, v___x_275_);
lean_dec_ref(v___x_274_);
if (v___x_276_ == 0)
{
lean_dec_ref(v_arg_273_);
lean_del_object(v___x_259_);
lean_dec_ref(v_x_245_);
goto v___jp_266_;
}
else
{
lean_object* v___x_277_; 
lean_del_object(v___x_264_);
v___x_277_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_273_);
if (lean_obj_tag(v___x_277_) == 1)
{
lean_object* v_val_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_302_; 
lean_del_object(v___x_259_);
v_val_278_ = lean_ctor_get(v___x_277_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_302_ == 0)
{
v___x_280_ = v___x_277_;
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_val_278_);
lean_dec(v___x_277_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_302_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom(v_x_245_, v_val_278_, v_synthetic_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_293_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_293_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v_a_283_);
v___x_288_ = v___x_280_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_292_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_290_; 
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_288_);
v___x_290_ = v___x_285_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_301_; 
lean_del_object(v___x_280_);
v_a_294_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_301_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_301_ == 0)
{
v___x_296_ = v___x_282_;
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_282_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_301_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_299_; 
if (v_isShared_297_ == 0)
{
v___x_299_ = v___x_296_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_a_294_);
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
}
else
{
lean_object* v___x_303_; lean_object* v___x_305_; 
lean_dec(v___x_277_);
lean_dec_ref(v_x_245_);
v___x_303_ = lean_box(0);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_303_);
v___x_305_ = v___x_259_;
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
v___jp_266_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 0, v___x_267_);
v___x_269_ = v___x_264_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_del_object(v___x_259_);
lean_dec_ref(v_x_245_);
v_a_308_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_261_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_261_);
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
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
lean_dec_ref(v_x_245_);
v_a_317_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_256_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_256_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom___boxed(lean_object* v_x_325_, lean_object* v_synthetic_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
uint8_t v_synthetic_boxed_336_; lean_object* v_res_337_; 
v_synthetic_boxed_336_ = lean_unbox(v_synthetic_326_);
v_res_337_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_bitVecAtom(v_x_325_, v_synthetic_boxed_336_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
return v_res_337_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_345_ = lean_box(0);
v___x_346_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__1));
v___x_347_ = l_Lean_mkConst(v___x_346_, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_box(0);
v___x_353_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__4));
v___x_354_ = l_Lean_Expr_const___override(v___x_353_, v___x_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(lean_object* v_w_355_, lean_object* v_val_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_bvExpr_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
lean_inc(v_val_356_);
lean_inc_n(v_w_355_, 2);
v_bvExpr_364_ = l_Std_Tactic_BVDecide_BVExpr_const___override(v_w_355_, v_val_356_);
v___x_365_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__2);
v___x_366_ = l_Lean_mkNatLit(v_w_355_);
v___x_367_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___closed__5);
v___x_368_ = l_Lean_mkNatLit(v_val_356_);
lean_inc_ref(v___x_366_);
v___x_369_ = l_Lean_mkAppB(v___x_367_, v___x_366_, v___x_368_);
lean_inc_ref(v___x_369_);
v___x_370_ = l_Lean_mkAppB(v___x_365_, v___x_366_, v___x_369_);
v___x_371_ = l_Lean_Meta_Sym_shareCommonInc(v___x_370_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = l_Lean_Meta_Sym_shareCommonInc(v___x_369_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_383_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_383_ == 0)
{
v___x_376_ = v___x_373_;
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_383_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___f_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___f_378_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkAtom___closed__3));
v___x_379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_379_, 0, v_w_355_);
lean_ctor_set(v___x_379_, 1, v_bvExpr_364_);
lean_ctor_set(v___x_379_, 2, v_a_374_);
lean_ctor_set(v___x_379_, 3, v___f_378_);
lean_ctor_set(v___x_379_, 4, v_a_372_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_379_);
v___x_381_ = v___x_376_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec(v_a_372_);
lean_dec_ref(v_bvExpr_364_);
lean_dec(v_w_355_);
v_a_384_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_373_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_373_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
lean_dec_ref(v___x_369_);
lean_dec_ref(v_bvExpr_364_);
lean_dec(v_w_355_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg___boxed(lean_object* v_w_400_, lean_object* v_val_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_w_400_, v_val_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(lean_object* v_w_410_, lean_object* v_val_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___redArg(v_w_410_, v_val_411_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst___boxed(lean_object* v_w_422_, lean_object* v_val_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_mkBVConst(v_w_422_, v_val_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_433_;
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

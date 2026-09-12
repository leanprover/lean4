// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Basic import Lean.Meta.Tactic.BVDecide.Reflect.ReifiedBVLogical import Lean.Meta.Tactic.BVDecide.Reflect.Reify import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS import Std.Tactic.BVDecide.Reflect
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
lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "BVLogicalExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sat_and"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BoolExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(65, 48, 52, 229, 233, 139, 247, 222)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__10_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(191, 125, 195, 121, 220, 103, 239, 120)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 172, 123, 74, 237, 247, 157, 191)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "false_of_eq_true_of_eq_false"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 74, 55, 212, 47, 213, 221, 101)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_4),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 107, 11, 53, 155, 200, 122, 195)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Unable to identify any relevant atoms."};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(lean_object* v_expr_1_, lean_object* v_val_2_, lean_object* v___x_3_, lean_object* v_arg_4_, lean_object* v_value_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_1_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v___x_15_, 1);
v___x_17_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_val_2_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_);
if (lean_obj_tag(v___x_17_) == 0)
{
lean_object* v_a_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_32_; 
v_a_18_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_32_ == 0)
{
v___x_20_ = v___x_17_;
v_isShared_21_ = v_isSharedCheck_32_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_a_18_);
lean_dec(v___x_17_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_32_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___y_23_; 
if (lean_obj_tag(v_a_18_) == 0)
{
lean_object* v___x_30_; 
lean_inc(v_a_16_);
v___x_30_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_16_);
v___y_23_ = v___x_30_;
goto v___jp_22_;
}
else
{
lean_object* v_val_31_; 
v_val_31_ = lean_ctor_get(v_a_18_, 0);
lean_inc(v_val_31_);
lean_dec_ref_known(v_a_18_, 1);
v___y_23_ = v_val_31_;
goto v___jp_22_;
}
v___jp_22_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_28_; 
v___x_24_ = lean_box(0);
v___x_25_ = l_Lean_mkConst(v___x_3_, v___x_24_);
v___x_26_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(v_a_16_, v_arg_4_, v___x_25_, v___y_23_, v_value_5_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 0, v___x_26_);
v___x_28_ = v___x_20_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v___x_26_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
else
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
lean_dec(v_a_16_);
lean_dec_ref(v_value_5_);
lean_dec_ref(v_arg_4_);
lean_dec(v___x_3_);
v_a_33_ = lean_ctor_get(v___x_17_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_17_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v___x_17_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_17_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
else
{
lean_dec_ref(v_value_5_);
lean_dec_ref(v_arg_4_);
lean_dec(v___x_3_);
lean_dec_ref(v_val_2_);
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed(lean_object* v_expr_41_, lean_object* v_val_42_, lean_object* v___x_43_, lean_object* v_arg_44_, lean_object* v_value_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(v_expr_41_, v_val_42_, v___x_43_, v_arg_44_, v_value_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object* v_hyp_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_type_80_; lean_object* v_value_81_; lean_object* v___x_82_; 
v_type_80_ = lean_ctor_get(v_hyp_66_, 1);
lean_inc_ref(v_type_80_);
v_value_81_ = lean_ctor_get(v_hyp_66_, 2);
lean_inc_ref(v_value_81_);
lean_dec_ref(v_hyp_66_);
v___x_82_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_80_, v_a_73_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_a_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_146_; 
v_a_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_146_ == 0)
{
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_146_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_a_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_146_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_87_ = l_Lean_Expr_cleanupAnnotations(v_a_83_);
v___x_88_ = l_Lean_Expr_isApp(v___x_87_);
if (v___x_88_ == 0)
{
lean_dec_ref(v___x_87_);
lean_del_object(v___x_85_);
lean_dec_ref(v_value_81_);
goto v___jp_77_;
}
else
{
lean_object* v_arg_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_arg_89_ = lean_ctor_get(v___x_87_, 1);
lean_inc_ref(v_arg_89_);
v___x_90_ = l_Lean_Expr_appFnCleanup___redArg(v___x_87_);
v___x_91_ = l_Lean_Expr_isApp(v___x_90_);
if (v___x_91_ == 0)
{
lean_dec_ref(v___x_90_);
lean_dec_ref(v_arg_89_);
lean_del_object(v___x_85_);
lean_dec_ref(v_value_81_);
goto v___jp_77_;
}
else
{
lean_object* v_arg_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
v_arg_92_ = lean_ctor_get(v___x_90_, 1);
lean_inc_ref(v_arg_92_);
v___x_93_ = l_Lean_Expr_appFnCleanup___redArg(v___x_90_);
v___x_94_ = l_Lean_Expr_isApp(v___x_93_);
if (v___x_94_ == 0)
{
lean_dec_ref(v___x_93_);
lean_dec_ref(v_arg_92_);
lean_dec_ref(v_arg_89_);
lean_del_object(v___x_85_);
lean_dec_ref(v_value_81_);
goto v___jp_77_;
}
else
{
lean_object* v_arg_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v_arg_95_ = lean_ctor_get(v___x_93_, 1);
lean_inc_ref(v_arg_95_);
v___x_96_ = l_Lean_Expr_appFnCleanup___redArg(v___x_93_);
v___x_97_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1));
v___x_98_ = l_Lean_Expr_isConstOf(v___x_96_, v___x_97_);
lean_dec_ref(v___x_96_);
if (v___x_98_ == 0)
{
lean_dec_ref(v_arg_95_);
lean_dec_ref(v_arg_92_);
lean_dec_ref(v_arg_89_);
lean_del_object(v___x_85_);
lean_dec_ref(v_value_81_);
goto v___jp_77_;
}
else
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_99_ = l_Lean_Expr_cleanupAnnotations(v_arg_95_);
v___x_100_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3));
v___x_101_ = l_Lean_Expr_isConstOf(v___x_99_, v___x_100_);
lean_dec_ref(v___x_99_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v___x_104_; 
lean_dec_ref(v_arg_92_);
lean_dec_ref(v_arg_89_);
lean_dec_ref(v_value_81_);
v___x_102_ = lean_box(0);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_102_);
v___x_104_ = v___x_85_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_106_ = l_Lean_Expr_cleanupAnnotations(v_arg_89_);
v___x_107_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5));
v___x_108_ = l_Lean_Expr_isConstOf(v___x_106_, v___x_107_);
lean_dec_ref(v___x_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_111_; 
lean_dec_ref(v_arg_92_);
lean_dec_ref(v_value_81_);
v___x_109_ = lean_box(0);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_109_);
v___x_111_ = v___x_85_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
else
{
lean_object* v___x_113_; 
lean_del_object(v___x_85_);
lean_inc_ref(v_arg_92_);
v___x_113_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v_arg_92_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_137_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_137_ == 0)
{
v___x_116_ = v___x_113_;
v_isShared_117_ = v_isSharedCheck_137_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_113_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_137_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
if (lean_obj_tag(v_a_114_) == 1)
{
lean_object* v_val_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_132_; 
v_val_118_ = lean_ctor_get(v_a_114_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_132_ == 0)
{
v___x_120_ = v_a_114_;
v_isShared_121_ = v_isSharedCheck_132_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_val_118_);
lean_dec(v_a_114_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_132_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v_bvExpr_122_; lean_object* v_expr_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_127_; 
v_bvExpr_122_ = lean_ctor_get(v_val_118_, 0);
lean_inc_ref(v_bvExpr_122_);
v_expr_123_ = lean_ctor_get(v_val_118_, 3);
lean_inc_ref_n(v_expr_123_, 2);
v___f_124_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed), 14, 5);
lean_closure_set(v___f_124_, 0, v_expr_123_);
lean_closure_set(v___f_124_, 1, v_val_118_);
lean_closure_set(v___f_124_, 2, v___x_107_);
lean_closure_set(v___f_124_, 3, v_arg_92_);
lean_closure_set(v___f_124_, 4, v_value_81_);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v_bvExpr_122_);
lean_ctor_set(v___x_125_, 1, v___f_124_);
lean_ctor_set(v___x_125_, 2, v_expr_123_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_125_);
v___x_127_ = v___x_120_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_127_);
v___x_129_ = v___x_116_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v___x_133_; lean_object* v___x_135_; 
lean_dec(v_a_114_);
lean_dec_ref(v_arg_92_);
lean_dec_ref(v_value_81_);
v___x_133_ = lean_box(0);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 0, v___x_133_);
v___x_135_ = v___x_116_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec_ref(v_arg_92_);
lean_dec_ref(v_value_81_);
v_a_138_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_113_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_113_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v_value_81_);
v_a_147_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_82_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_82_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
v___jp_77_:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object* v_hyp_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_hyp_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec(v_a_162_);
lean_dec_ref(v_a_161_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
lean_dec(v_a_156_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0(lean_object* v_satAtAtoms_169_, lean_object* v_satAtAtoms_170_, lean_object* v___x_171_, lean_object* v___x_172_, lean_object* v___x_173_, lean_object* v___x_174_, lean_object* v_expr_175_, lean_object* v_expr_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc_ref(v___y_179_);
lean_inc(v___y_178_);
lean_inc_ref(v___y_177_);
v___x_188_ = lean_apply_9(v_satAtAtoms_169_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, lean_box(0));
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_188_, 1);
lean_inc(v___y_184_);
lean_inc_ref(v___y_183_);
lean_inc(v___y_182_);
lean_inc_ref(v___y_181_);
lean_inc(v___y_180_);
lean_inc_ref(v___y_179_);
lean_inc(v___y_178_);
lean_inc_ref(v___y_177_);
v___x_190_ = lean_apply_9(v_satAtAtoms_170_, v___y_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, lean_box(0));
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_203_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_203_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_195_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0));
v___x_196_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1));
v___x_197_ = l_Lean_Name_mkStr5(v___x_171_, v___x_172_, v___x_173_, v___x_195_, v___x_196_);
v___x_198_ = l_Lean_mkConst(v___x_197_, v___x_174_);
v___x_199_ = l_Lean_mkApp5(v___x_198_, v_expr_175_, v_expr_176_, v_a_187_, v_a_189_, v_a_191_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_199_);
v___x_201_ = v___x_193_;
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
else
{
lean_dec(v_a_189_);
lean_dec(v_a_187_);
lean_dec_ref(v_expr_176_);
lean_dec_ref(v_expr_175_);
lean_dec(v___x_174_);
lean_dec_ref(v___x_173_);
lean_dec_ref(v___x_172_);
lean_dec_ref(v___x_171_);
return v___x_190_;
}
}
else
{
lean_dec(v_a_187_);
lean_dec_ref(v_expr_176_);
lean_dec_ref(v_expr_175_);
lean_dec(v___x_174_);
lean_dec_ref(v___x_173_);
lean_dec_ref(v___x_172_);
lean_dec_ref(v___x_171_);
lean_dec_ref(v_satAtAtoms_170_);
return v___x_188_;
}
}
else
{
lean_dec_ref(v_expr_176_);
lean_dec_ref(v_expr_175_);
lean_dec(v___x_174_);
lean_dec_ref(v___x_173_);
lean_dec_ref(v___x_172_);
lean_dec_ref(v___x_171_);
lean_dec_ref(v_satAtAtoms_170_);
lean_dec_ref(v_satAtAtoms_169_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_satAtAtoms_204_ = _args[0];
lean_object* v_satAtAtoms_205_ = _args[1];
lean_object* v___x_206_ = _args[2];
lean_object* v___x_207_ = _args[3];
lean_object* v___x_208_ = _args[4];
lean_object* v___x_209_ = _args[5];
lean_object* v_expr_210_ = _args[6];
lean_object* v_expr_211_ = _args[7];
lean_object* v___y_212_ = _args[8];
lean_object* v___y_213_ = _args[9];
lean_object* v___y_214_ = _args[10];
lean_object* v___y_215_ = _args[11];
lean_object* v___y_216_ = _args[12];
lean_object* v___y_217_ = _args[13];
lean_object* v___y_218_ = _args[14];
lean_object* v___y_219_ = _args[15];
lean_object* v___y_220_ = _args[16];
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0(v_satAtAtoms_204_, v_satAtAtoms_205_, v___x_206_, v___x_207_, v___x_208_, v___x_209_, v_expr_210_, v_expr_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_221_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_box(0);
v___x_234_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5));
v___x_235_ = l_Lean_mkConst(v___x_234_, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_box(0);
v___x_243_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8));
v___x_244_ = l_Lean_mkConst(v___x_243_, v___x_242_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_box(0);
v___x_254_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12));
v___x_255_ = l_Lean_mkConst(v___x_254_, v___x_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object* v_x_256_, lean_object* v_y_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_bvExpr_265_; lean_object* v_satAtAtoms_266_; lean_object* v_expr_267_; lean_object* v_bvExpr_268_; lean_object* v_satAtAtoms_269_; lean_object* v_expr_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_305_; 
v_bvExpr_265_ = lean_ctor_get(v_x_256_, 0);
lean_inc_ref(v_bvExpr_265_);
v_satAtAtoms_266_ = lean_ctor_get(v_x_256_, 1);
lean_inc_ref(v_satAtAtoms_266_);
v_expr_267_ = lean_ctor_get(v_x_256_, 2);
lean_inc_ref(v_expr_267_);
lean_dec_ref(v_x_256_);
v_bvExpr_268_ = lean_ctor_get(v_y_257_, 0);
v_satAtAtoms_269_ = lean_ctor_get(v_y_257_, 1);
v_expr_270_ = lean_ctor_get(v_y_257_, 2);
v_isSharedCheck_305_ = !lean_is_exclusive(v_y_257_);
if (v_isSharedCheck_305_ == 0)
{
v___x_272_ = v_y_257_;
v_isShared_273_ = v_isSharedCheck_305_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_expr_270_);
lean_inc(v_satAtAtoms_269_);
lean_inc(v_bvExpr_268_);
lean_dec(v_y_257_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_305_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
uint8_t v___x_274_; lean_object* v_bvExpr_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_274_ = 0;
v_bvExpr_275_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_bvExpr_275_, 0, v_bvExpr_265_);
lean_ctor_set(v_bvExpr_275_, 1, v_bvExpr_268_);
lean_ctor_set_uint8(v_bvExpr_275_, sizeof(void*)*2, v___x_274_);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0));
v___x_277_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1));
v___x_278_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2));
v___x_279_ = lean_box(0);
lean_inc_ref(v_expr_270_);
lean_inc_ref(v_expr_267_);
v___f_280_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___boxed), 17, 8);
lean_closure_set(v___f_280_, 0, v_satAtAtoms_266_);
lean_closure_set(v___f_280_, 1, v_satAtAtoms_269_);
lean_closure_set(v___f_280_, 2, v___x_276_);
lean_closure_set(v___f_280_, 3, v___x_277_);
lean_closure_set(v___f_280_, 4, v___x_278_);
lean_closure_set(v___f_280_, 5, v___x_279_);
lean_closure_set(v___f_280_, 6, v_expr_267_);
lean_closure_set(v___f_280_, 7, v_expr_270_);
v___x_281_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6);
v___x_282_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9);
v___x_283_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13);
v___x_284_ = l_Lean_mkApp4(v___x_281_, v___x_282_, v___x_283_, v_expr_267_, v_expr_270_);
v___x_285_ = l_Lean_Meta_Sym_shareCommonInc(v___x_284_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_296_; 
v_a_286_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_296_ == 0)
{
v___x_288_ = v___x_285_;
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_285_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_296_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_273_ == 0)
{
lean_ctor_set(v___x_272_, 2, v_a_286_);
lean_ctor_set(v___x_272_, 1, v___f_280_);
lean_ctor_set(v___x_272_, 0, v_bvExpr_275_);
v___x_291_ = v___x_272_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_bvExpr_275_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___f_280_);
lean_ctor_set(v_reuseFailAlloc_295_, 2, v_a_286_);
v___x_291_ = v_reuseFailAlloc_295_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_293_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_291_);
v___x_293_ = v___x_288_;
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
lean_object* v_a_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v___f_280_);
lean_dec_ref_known(v_bvExpr_275_, 2);
lean_del_object(v___x_272_);
v_a_297_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_304_ == 0)
{
v___x_299_ = v___x_285_;
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_a_297_);
lean_dec(v___x_285_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_304_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_302_; 
if (v_isShared_300_ == 0)
{
v___x_302_ = v___x_299_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_a_297_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___boxed(lean_object* v_x_306_, lean_object* v_y_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_x_306_, v_y_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_a_312_);
lean_dec(v_a_311_);
lean_dec_ref(v_a_310_);
lean_dec(v_a_309_);
lean_dec_ref(v_a_308_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(lean_object* v_x_316_, lean_object* v_y_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_x_316_, v_y_317_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___boxed(lean_object* v_x_328_, lean_object* v_y_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(v_x_328_, v_y_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_337_);
lean_dec_ref(v_a_336_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_env_347_; lean_object* v___x_348_; lean_object* v_toCold_349_; lean_object* v_mctx_350_; lean_object* v_lctx_351_; lean_object* v_options_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_346_ = lean_st_ref_get(v___y_344_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v___x_348_ = lean_st_ref_get(v___y_342_);
v_toCold_349_ = lean_ctor_get(v___y_343_, 0);
v_mctx_350_ = lean_ctor_get(v___x_348_, 0);
lean_inc_ref(v_mctx_350_);
lean_dec(v___x_348_);
v_lctx_351_ = lean_ctor_get(v___y_341_, 2);
v_options_352_ = lean_ctor_get(v_toCold_349_, 2);
lean_inc_ref(v_options_352_);
lean_inc_ref(v_lctx_351_);
v___x_353_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_353_, 0, v_env_347_);
lean_ctor_set(v___x_353_, 1, v_mctx_350_);
lean_ctor_set(v___x_353_, 2, v_lctx_351_);
lean_ctor_set(v___x_353_, 3, v_options_352_);
v___x_354_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v_msgData_340_);
v___x_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(lean_object* v_msgData_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msgData_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(lean_object* v_msg_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
v_ref_369_ = lean_ctor_get(v___y_366_, 2);
v___x_370_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msg_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_379_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
lean_inc(v_ref_369_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_ref_369_);
lean_ctor_set(v___x_375_, 1, v_a_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 1);
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_386_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_box(0);
v___x_395_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1));
v___x_396_ = l_Lean_mkConst(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_box(0);
v___x_407_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5));
v___x_408_ = l_Lean_mkConst(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7));
v___x_411_ = l_Lean_stringToMessageData(v___x_410_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(lean_object* v_x_412_, lean_object* v_h_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; lean_object* v_atoms_424_; lean_object* v_size_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_423_ = lean_st_ref_get(v_a_415_);
v_atoms_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc_ref(v_atoms_424_);
lean_dec(v___x_423_);
v_size_425_ = lean_ctor_get(v_atoms_424_, 0);
lean_inc(v_size_425_);
lean_dec_ref(v_atoms_424_);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_nat_dec_eq(v_size_425_, v___x_426_);
lean_dec(v_size_425_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; lean_object* v_satAtAtoms_430_; lean_object* v_expr_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc_n(v_a_429_, 2);
lean_dec_ref_known(v___x_428_, 1);
v_satAtAtoms_430_ = lean_ctor_get(v_x_412_, 1);
lean_inc_ref(v_satAtAtoms_430_);
v_expr_431_ = lean_ctor_get(v_x_412_, 2);
lean_inc_ref(v_expr_431_);
lean_dec_ref(v_x_412_);
v___x_432_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2);
v___x_433_ = l_Lean_mkAppB(v___x_432_, v_a_429_, v_expr_431_);
v___x_434_ = l_Lean_Meta_Sym_shareCommonInc(v___x_433_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
lean_inc(v_a_421_);
lean_inc_ref(v_a_420_);
lean_inc(v_a_419_);
lean_inc_ref(v_a_418_);
lean_inc(v_a_417_);
lean_inc_ref(v_a_416_);
lean_inc(v_a_415_);
lean_inc_ref(v_a_414_);
v___x_436_ = lean_apply_9(v_satAtAtoms_430_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_, lean_box(0));
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_447_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_447_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_447_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_441_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6);
v___x_442_ = l_Lean_Expr_app___override(v_h_413_, v_a_429_);
v___x_443_ = l_Lean_mkApp3(v___x_441_, v_a_435_, v_a_437_, v___x_442_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_443_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
else
{
lean_dec(v_a_435_);
lean_dec(v_a_429_);
lean_dec_ref(v_h_413_);
return v___x_436_;
}
}
else
{
lean_dec_ref(v_satAtAtoms_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_h_413_);
return v___x_434_;
}
}
else
{
lean_dec_ref(v_h_413_);
lean_dec_ref(v_x_412_);
return v___x_428_;
}
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec_ref(v_h_413_);
lean_dec_ref(v_x_412_);
v___x_448_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8);
v___x_449_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v___x_448_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
return v___x_449_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object* v_x_450_, lean_object* v_h_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_x_450_, v_h_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec_ref(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec_ref(v_a_452_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(lean_object* v_00_u03b1_462_, lean_object* v_msg_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_463_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object* v_00_u03b1_474_, lean_object* v_msg_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(v_00_u03b1_474_, v_msg_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_485_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin) {
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
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Reflect(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_ReifiedBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Reflect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed(lean_object**);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "BVLogicalExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sat_and"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(lean_object* v_expr_1_, lean_object* v_val_2_, lean_object* v___x_3_, lean_object* v_arg_4_, lean_object* v_value_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_1_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_20_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_a_19_);
lean_dec_ref_known(v___x_18_, 1);
v___x_20_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_val_2_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_35_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_35_ == 0)
{
v___x_23_ = v___x_20_;
v_isShared_24_ = v_isSharedCheck_35_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_35_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___y_26_; 
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v___x_33_; 
lean_inc(v_a_19_);
v___x_33_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_19_);
v___y_26_ = v___x_33_;
goto v___jp_25_;
}
else
{
lean_object* v_val_34_; 
v_val_34_ = lean_ctor_get(v_a_21_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v_a_21_, 1);
v___y_26_ = v_val_34_;
goto v___jp_25_;
}
v___jp_25_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
v___x_27_ = lean_box(0);
v___x_28_ = l_Lean_mkConst(v___x_3_, v___x_27_);
v___x_29_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(v_a_19_, v_arg_4_, v___x_28_, v___y_26_, v_value_5_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 0, v___x_29_);
v___x_31_ = v___x_23_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec(v_a_19_);
lean_dec_ref(v_value_5_);
lean_dec_ref(v_arg_4_);
lean_dec(v___x_3_);
v_a_36_ = lean_ctor_get(v___x_20_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_20_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_20_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
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
lean_dec_ref(v_value_5_);
lean_dec_ref(v_arg_4_);
lean_dec(v___x_3_);
lean_dec_ref(v_val_2_);
return v___x_18_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_1_ = stack[0].m_obj;
lean_object* v_val_2_ = stack[1].m_obj;
lean_object* v___x_3_ = stack[2].m_obj;
lean_object* v_arg_4_ = stack[3].m_obj;
lean_object* v_value_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v___y_11_ = stack[10].m_obj;
lean_object* v___y_12_ = stack[11].m_obj;
lean_object* v___y_13_ = stack[12].m_obj;
lean_object* v___y_14_ = stack[13].m_obj;
lean_object* v___y_15_ = stack[14].m_obj;
lean_object* v___y_16_ = stack[15].m_obj;
lean_object* v_res_44_;
v_res_44_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(v_expr_1_, v_val_2_, v___x_3_, v_arg_4_, v_value_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed(lean_object** _args){
lean_object* v_expr_45_ = _args[0];
lean_object* v_val_46_ = _args[1];
lean_object* v___x_47_ = _args[2];
lean_object* v_arg_48_ = _args[3];
lean_object* v_value_49_ = _args[4];
lean_object* v___y_50_ = _args[5];
lean_object* v___y_51_ = _args[6];
lean_object* v___y_52_ = _args[7];
lean_object* v___y_53_ = _args[8];
lean_object* v___y_54_ = _args[9];
lean_object* v___y_55_ = _args[10];
lean_object* v___y_56_ = _args[11];
lean_object* v___y_57_ = _args[12];
lean_object* v___y_58_ = _args[13];
lean_object* v___y_59_ = _args[14];
lean_object* v___y_60_ = _args[15];
lean_object* v___y_61_ = _args[16];
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(v_expr_45_, v_val_46_, v___x_47_, v_arg_48_, v_value_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_62_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object* v_hyp_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_type_90_; lean_object* v_value_91_; lean_object* v___x_92_; 
v_type_90_ = lean_ctor_get(v_hyp_73_, 1);
lean_inc_ref(v_type_90_);
v_value_91_ = lean_ctor_get(v_hyp_73_, 2);
lean_inc_ref(v_value_91_);
lean_dec_ref(v_hyp_73_);
v___x_92_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_type_90_, v_a_83_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_156_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_156_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_156_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_156_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = l_Lean_Expr_cleanupAnnotations(v_a_93_);
v___x_98_ = l_Lean_Expr_isApp(v___x_97_);
if (v___x_98_ == 0)
{
lean_dec_ref(v___x_97_);
lean_del_object(v___x_95_);
lean_dec_ref(v_value_91_);
goto v___jp_87_;
}
else
{
lean_object* v_arg_99_; lean_object* v___x_100_; uint8_t v___x_101_; 
v_arg_99_ = lean_ctor_get(v___x_97_, 1);
lean_inc_ref(v_arg_99_);
v___x_100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_97_);
v___x_101_ = l_Lean_Expr_isApp(v___x_100_);
if (v___x_101_ == 0)
{
lean_dec_ref(v___x_100_);
lean_dec_ref(v_arg_99_);
lean_del_object(v___x_95_);
lean_dec_ref(v_value_91_);
goto v___jp_87_;
}
else
{
lean_object* v_arg_102_; lean_object* v___x_103_; uint8_t v___x_104_; 
v_arg_102_ = lean_ctor_get(v___x_100_, 1);
lean_inc_ref(v_arg_102_);
v___x_103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_100_);
v___x_104_ = l_Lean_Expr_isApp(v___x_103_);
if (v___x_104_ == 0)
{
lean_dec_ref(v___x_103_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
lean_del_object(v___x_95_);
lean_dec_ref(v_value_91_);
goto v___jp_87_;
}
else
{
lean_object* v_arg_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_arg_105_ = lean_ctor_get(v___x_103_, 1);
lean_inc_ref(v_arg_105_);
v___x_106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_103_);
v___x_107_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1));
v___x_108_ = l_Lean_Expr_isConstOf(v___x_106_, v___x_107_);
lean_dec_ref(v___x_106_);
if (v___x_108_ == 0)
{
lean_dec_ref(v_arg_105_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
lean_del_object(v___x_95_);
lean_dec_ref(v_value_91_);
goto v___jp_87_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = l_Lean_Expr_cleanupAnnotations(v_arg_105_);
v___x_110_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3));
v___x_111_ = l_Lean_Expr_isConstOf(v___x_109_, v___x_110_);
lean_dec_ref(v___x_109_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_114_; 
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_arg_99_);
lean_dec_ref(v_value_91_);
v___x_112_ = lean_box(0);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_112_);
v___x_114_ = v___x_95_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = l_Lean_Expr_cleanupAnnotations(v_arg_99_);
v___x_117_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5));
v___x_118_ = l_Lean_Expr_isConstOf(v___x_116_, v___x_117_);
lean_dec_ref(v___x_116_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_121_; 
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_value_91_);
v___x_119_ = lean_box(0);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_119_);
v___x_121_ = v___x_95_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
else
{
lean_object* v___x_123_; 
lean_del_object(v___x_95_);
lean_inc_ref(v_arg_102_);
v___x_123_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v_arg_102_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_147_; 
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_147_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_147_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_147_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
if (lean_obj_tag(v_a_124_) == 1)
{
lean_object* v_val_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_142_; 
v_val_128_ = lean_ctor_get(v_a_124_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_a_124_);
if (v_isSharedCheck_142_ == 0)
{
v___x_130_ = v_a_124_;
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_val_128_);
lean_dec(v_a_124_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_142_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_bvExpr_132_; lean_object* v_expr_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v_bvExpr_132_ = lean_ctor_get(v_val_128_, 0);
lean_inc_ref(v_bvExpr_132_);
v_expr_133_ = lean_ctor_get(v_val_128_, 3);
lean_inc_ref_n(v_expr_133_, 2);
v___f_134_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed), 17, 5);
lean_closure_set(v___f_134_, 0, v_expr_133_);
lean_closure_set(v___f_134_, 1, v_val_128_);
lean_closure_set(v___f_134_, 2, v___x_117_);
lean_closure_set(v___f_134_, 3, v_arg_102_);
lean_closure_set(v___f_134_, 4, v_value_91_);
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v_bvExpr_132_);
lean_ctor_set(v___x_135_, 1, v___f_134_);
lean_ctor_set(v___x_135_, 2, v_expr_133_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_135_);
v___x_137_ = v___x_130_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_135_);
v___x_137_ = v_reuseFailAlloc_141_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_139_; 
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_137_);
v___x_139_ = v___x_126_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
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
lean_object* v___x_143_; lean_object* v___x_145_; 
lean_dec(v_a_124_);
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_value_91_);
v___x_143_ = lean_box(0);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_143_);
v___x_145_ = v___x_126_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec_ref(v_arg_102_);
lean_dec_ref(v_value_91_);
v_a_148_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_123_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_123_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
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
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v_value_91_);
v_a_157_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_92_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_92_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
v___jp_87_:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_0interp(lean_interpreter_value* stack)
{
lean_object* v_hyp_73_ = stack[0].m_obj;
lean_object* v_a_74_ = stack[1].m_obj;
lean_object* v_a_75_ = stack[2].m_obj;
lean_object* v_a_76_ = stack[3].m_obj;
lean_object* v_a_77_ = stack[4].m_obj;
lean_object* v_a_78_ = stack[5].m_obj;
lean_object* v_a_79_ = stack[6].m_obj;
lean_object* v_a_80_ = stack[7].m_obj;
lean_object* v_a_81_ = stack[8].m_obj;
lean_object* v_a_82_ = stack[9].m_obj;
lean_object* v_a_83_ = stack[10].m_obj;
lean_object* v_a_84_ = stack[11].m_obj;
lean_object* v_a_85_ = stack[12].m_obj;
lean_object* v_res_165_;
v_res_165_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_hyp_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object* v_hyp_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_hyp_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec_ref(v_a_177_);
lean_dec(v_a_176_);
lean_dec_ref(v_a_175_);
lean_dec(v_a_174_);
lean_dec_ref(v_a_173_);
lean_dec(v_a_172_);
lean_dec_ref(v_a_171_);
lean_dec(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
return v_res_180_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0(lean_object* v_satAtAtoms_183_, lean_object* v_satAtAtoms_184_, lean_object* v___x_185_, lean_object* v___x_186_, lean_object* v___x_187_, lean_object* v___x_188_, lean_object* v_expr_189_, lean_object* v_expr_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_205_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_a_204_);
lean_dec_ref_known(v___x_203_, 1);
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
lean_inc(v___y_199_);
lean_inc_ref(v___y_198_);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc(v___y_192_);
lean_inc_ref(v___y_191_);
v___x_205_ = lean_apply_12(v_satAtAtoms_183_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, lean_box(0));
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_a_206_; lean_object* v___x_207_; 
v_a_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_a_206_);
lean_dec_ref_known(v___x_205_, 1);
lean_inc(v___y_201_);
lean_inc_ref(v___y_200_);
lean_inc(v___y_199_);
lean_inc_ref(v___y_198_);
lean_inc(v___y_197_);
lean_inc_ref(v___y_196_);
lean_inc(v___y_195_);
lean_inc_ref(v___y_194_);
lean_inc(v___y_193_);
lean_inc(v___y_192_);
lean_inc_ref(v___y_191_);
v___x_207_ = lean_apply_12(v_satAtAtoms_184_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_, lean_box(0));
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_220_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_220_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_220_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__0));
v___x_213_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___closed__1));
v___x_214_ = l_Lean_Name_mkStr5(v___x_185_, v___x_186_, v___x_187_, v___x_212_, v___x_213_);
v___x_215_ = l_Lean_mkConst(v___x_214_, v___x_188_);
v___x_216_ = l_Lean_mkApp5(v___x_215_, v_expr_189_, v_expr_190_, v_a_204_, v_a_206_, v_a_208_);
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_216_);
v___x_218_ = v___x_210_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v___x_216_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
else
{
lean_dec(v_a_206_);
lean_dec(v_a_204_);
lean_dec_ref(v_expr_190_);
lean_dec_ref(v_expr_189_);
lean_dec(v___x_188_);
lean_dec_ref(v___x_187_);
lean_dec_ref(v___x_186_);
lean_dec_ref(v___x_185_);
return v___x_207_;
}
}
else
{
lean_dec(v_a_204_);
lean_dec_ref(v_expr_190_);
lean_dec_ref(v_expr_189_);
lean_dec(v___x_188_);
lean_dec_ref(v___x_187_);
lean_dec_ref(v___x_186_);
lean_dec_ref(v___x_185_);
lean_dec_ref(v_satAtAtoms_184_);
return v___x_205_;
}
}
else
{
lean_dec_ref(v_expr_190_);
lean_dec_ref(v_expr_189_);
lean_dec(v___x_188_);
lean_dec_ref(v___x_187_);
lean_dec_ref(v___x_186_);
lean_dec_ref(v___x_185_);
lean_dec_ref(v_satAtAtoms_184_);
lean_dec_ref(v_satAtAtoms_183_);
return v___x_203_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_satAtAtoms_183_ = stack[0].m_obj;
lean_object* v_satAtAtoms_184_ = stack[1].m_obj;
lean_object* v___x_185_ = stack[2].m_obj;
lean_object* v___x_186_ = stack[3].m_obj;
lean_object* v___x_187_ = stack[4].m_obj;
lean_object* v___x_188_ = stack[5].m_obj;
lean_object* v_expr_189_ = stack[6].m_obj;
lean_object* v_expr_190_ = stack[7].m_obj;
lean_object* v___y_191_ = stack[8].m_obj;
lean_object* v___y_192_ = stack[9].m_obj;
lean_object* v___y_193_ = stack[10].m_obj;
lean_object* v___y_194_ = stack[11].m_obj;
lean_object* v___y_195_ = stack[12].m_obj;
lean_object* v___y_196_ = stack[13].m_obj;
lean_object* v___y_197_ = stack[14].m_obj;
lean_object* v___y_198_ = stack[15].m_obj;
lean_object* v___y_199_ = stack[16].m_obj;
lean_object* v___y_200_ = stack[17].m_obj;
lean_object* v___y_201_ = stack[18].m_obj;
lean_object* v_res_221_;
v_res_221_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0(v_satAtAtoms_183_, v_satAtAtoms_184_, v___x_185_, v___x_186_, v___x_187_, v___x_188_, v_expr_189_, v_expr_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___boxed(lean_object** _args){
lean_object* v_satAtAtoms_222_ = _args[0];
lean_object* v_satAtAtoms_223_ = _args[1];
lean_object* v___x_224_ = _args[2];
lean_object* v___x_225_ = _args[3];
lean_object* v___x_226_ = _args[4];
lean_object* v___x_227_ = _args[5];
lean_object* v_expr_228_ = _args[6];
lean_object* v_expr_229_ = _args[7];
lean_object* v___y_230_ = _args[8];
lean_object* v___y_231_ = _args[9];
lean_object* v___y_232_ = _args[10];
lean_object* v___y_233_ = _args[11];
lean_object* v___y_234_ = _args[12];
lean_object* v___y_235_ = _args[13];
lean_object* v___y_236_ = _args[14];
lean_object* v___y_237_ = _args[15];
lean_object* v___y_238_ = _args[16];
lean_object* v___y_239_ = _args[17];
lean_object* v___y_240_ = _args[18];
lean_object* v___y_241_ = _args[19];
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0(v_satAtAtoms_222_, v_satAtAtoms_223_, v___x_224_, v___x_225_, v___x_226_, v___x_227_, v_expr_228_, v_expr_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_242_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = lean_box(0);
v___x_255_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__5));
v___x_256_ = l_Lean_mkConst(v___x_255_, v___x_254_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
v___x_264_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__8));
v___x_265_ = l_Lean_mkConst(v___x_264_, v___x_263_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_box(0);
v___x_275_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__12));
v___x_276_ = l_Lean_mkConst(v___x_275_, v___x_274_);
return v___x_276_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(lean_object* v_x_277_, lean_object* v_y_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_bvExpr_286_; lean_object* v_satAtAtoms_287_; lean_object* v_expr_288_; lean_object* v_bvExpr_289_; lean_object* v_satAtAtoms_290_; lean_object* v_expr_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_326_; 
v_bvExpr_286_ = lean_ctor_get(v_x_277_, 0);
lean_inc_ref(v_bvExpr_286_);
v_satAtAtoms_287_ = lean_ctor_get(v_x_277_, 1);
lean_inc_ref(v_satAtAtoms_287_);
v_expr_288_ = lean_ctor_get(v_x_277_, 2);
lean_inc_ref(v_expr_288_);
lean_dec_ref(v_x_277_);
v_bvExpr_289_ = lean_ctor_get(v_y_278_, 0);
v_satAtAtoms_290_ = lean_ctor_get(v_y_278_, 1);
v_expr_291_ = lean_ctor_get(v_y_278_, 2);
v_isSharedCheck_326_ = !lean_is_exclusive(v_y_278_);
if (v_isSharedCheck_326_ == 0)
{
v___x_293_ = v_y_278_;
v_isShared_294_ = v_isSharedCheck_326_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_expr_291_);
lean_inc(v_satAtAtoms_290_);
lean_inc(v_bvExpr_289_);
lean_dec(v_y_278_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_326_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
uint8_t v___x_295_; lean_object* v_bvExpr_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___f_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_295_ = 0;
v_bvExpr_296_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v_bvExpr_296_, 0, v_bvExpr_286_);
lean_ctor_set(v_bvExpr_296_, 1, v_bvExpr_289_);
lean_ctor_set_uint8(v_bvExpr_296_, sizeof(void*)*2, v___x_295_);
v___x_297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__0));
v___x_298_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__1));
v___x_299_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__2));
v___x_300_ = lean_box(0);
lean_inc_ref(v_expr_291_);
lean_inc_ref(v_expr_288_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___lam__0___boxed), 20, 8);
lean_closure_set(v___f_301_, 0, v_satAtAtoms_287_);
lean_closure_set(v___f_301_, 1, v_satAtAtoms_290_);
lean_closure_set(v___f_301_, 2, v___x_297_);
lean_closure_set(v___f_301_, 3, v___x_298_);
lean_closure_set(v___f_301_, 4, v___x_299_);
lean_closure_set(v___f_301_, 5, v___x_300_);
lean_closure_set(v___f_301_, 6, v_expr_288_);
lean_closure_set(v___f_301_, 7, v_expr_291_);
v___x_302_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__6);
v___x_303_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__9);
v___x_304_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___closed__13);
v___x_305_ = l_Lean_mkApp4(v___x_302_, v___x_303_, v___x_304_, v_expr_288_, v_expr_291_);
v___x_306_ = l_Lean_Meta_Sym_shareCommonInc(v___x_305_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_317_ == 0)
{
v___x_309_ = v___x_306_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_a_307_);
lean_dec(v___x_306_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_312_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 2, v_a_307_);
lean_ctor_set(v___x_293_, 1, v___f_301_);
lean_ctor_set(v___x_293_, 0, v_bvExpr_296_);
v___x_312_ = v___x_293_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_bvExpr_296_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___f_301_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_a_307_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_314_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 0, v___x_312_);
v___x_314_ = v___x_309_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec_ref(v___f_301_);
lean_dec_ref_known(v_bvExpr_296_, 2);
lean_del_object(v___x_293_);
v_a_318_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_306_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_306_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_277_ = stack[0].m_obj;
lean_object* v_y_278_ = stack[1].m_obj;
lean_object* v_a_279_ = stack[2].m_obj;
lean_object* v_a_280_ = stack[3].m_obj;
lean_object* v_a_281_ = stack[4].m_obj;
lean_object* v_a_282_ = stack[5].m_obj;
lean_object* v_a_283_ = stack[6].m_obj;
lean_object* v_a_284_ = stack[7].m_obj;
lean_object* v_res_327_;
v_res_327_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_x_277_, v_y_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg___boxed(lean_object* v_x_328_, lean_object* v_y_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_x_328_, v_y_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
return v_res_337_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(lean_object* v_x_338_, lean_object* v_y_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___redArg(v_x_338_, v_y_339_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
return v___x_352_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_338_ = stack[0].m_obj;
lean_object* v_y_339_ = stack[1].m_obj;
lean_object* v_a_340_ = stack[2].m_obj;
lean_object* v_a_341_ = stack[3].m_obj;
lean_object* v_a_342_ = stack[4].m_obj;
lean_object* v_a_343_ = stack[5].m_obj;
lean_object* v_a_344_ = stack[6].m_obj;
lean_object* v_a_345_ = stack[7].m_obj;
lean_object* v_a_346_ = stack[8].m_obj;
lean_object* v_a_347_ = stack[9].m_obj;
lean_object* v_a_348_ = stack[10].m_obj;
lean_object* v_a_349_ = stack[11].m_obj;
lean_object* v_a_350_ = stack[12].m_obj;
lean_object* v_res_353_;
v_res_353_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(v_x_338_, v_y_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_);
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___boxed(lean_object* v_x_354_, lean_object* v_y_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(v_x_354_, v_y_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_368_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(lean_object* v_msgData_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_env_376_; uint8_t v___x_377_; lean_object* v_env_378_; lean_object* v___x_379_; lean_object* v_toCold_380_; lean_object* v_mctx_381_; lean_object* v_lctx_382_; lean_object* v_options_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_375_ = lean_st_ref_get(v___y_373_);
v_env_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc_ref(v_env_376_);
lean_dec(v___x_375_);
v___x_377_ = 0;
v_env_378_ = l_Lean_Environment_setRecordingDeps(v_env_376_, v___x_377_);
v___x_379_ = lean_st_ref_get(v___y_371_);
v_toCold_380_ = lean_ctor_get(v___y_372_, 0);
v_mctx_381_ = lean_ctor_get(v___x_379_, 0);
lean_inc_ref(v_mctx_381_);
lean_dec(v___x_379_);
v_lctx_382_ = lean_ctor_get(v___y_370_, 2);
v_options_383_ = lean_ctor_get(v_toCold_380_, 2);
lean_inc_ref(v_options_383_);
lean_inc_ref(v_lctx_382_);
v___x_384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_384_, 0, v_env_378_);
lean_ctor_set(v___x_384_, 1, v_mctx_381_);
lean_ctor_set(v___x_384_, 2, v_lctx_382_);
lean_ctor_set(v___x_384_, 3, v_options_383_);
v___x_385_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_msgData_369_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_369_ = stack[0].m_obj;
lean_object* v___y_370_ = stack[1].m_obj;
lean_object* v___y_371_ = stack[2].m_obj;
lean_object* v___y_372_ = stack[3].m_obj;
lean_object* v___y_373_ = stack[4].m_obj;
lean_object* v_res_387_;
v_res_387_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msgData_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
stack->m_obj
 = v_res_387_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(lean_object* v_msgData_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msgData_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_ref_401_; lean_object* v___x_402_; lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_ref_401_ = lean_ctor_get(v___y_398_, 2);
v___x_402_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_411_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
lean_inc(v_ref_401_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_ref_401_);
lean_ctor_set(v___x_407_, 1, v_a_403_);
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_395_ = stack[0].m_obj;
lean_object* v___y_396_ = stack[1].m_obj;
lean_object* v___y_397_ = stack[2].m_obj;
lean_object* v___y_398_ = stack[3].m_obj;
lean_object* v___y_399_ = stack[4].m_obj;
lean_object* v_res_412_;
v_res_412_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
stack->m_obj
 = v_res_412_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_419_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_box(0);
v___x_428_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1));
v___x_429_ = l_Lean_mkConst(v___x_428_, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_439_ = lean_box(0);
v___x_440_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5));
v___x_441_ = l_Lean_mkConst(v___x_440_, v___x_439_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(lean_object* v_x_445_, lean_object* v_h_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v___x_459_; lean_object* v_atoms_460_; lean_object* v_size_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_459_ = lean_st_ref_get(v_a_448_);
v_atoms_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_atoms_460_);
lean_dec(v___x_459_);
v_size_461_ = lean_ctor_get(v_atoms_460_, 0);
lean_inc(v_size_461_);
lean_dec_ref(v_atoms_460_);
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_nat_dec_eq(v_size_461_, v___x_462_);
lean_dec(v_size_461_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_464_) == 0)
{
lean_object* v_a_465_; lean_object* v_satAtAtoms_466_; lean_object* v_expr_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v_a_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_n(v_a_465_, 2);
lean_dec_ref_known(v___x_464_, 1);
v_satAtAtoms_466_ = lean_ctor_get(v_x_445_, 1);
lean_inc_ref(v_satAtAtoms_466_);
v_expr_467_ = lean_ctor_get(v_x_445_, 2);
lean_inc_ref(v_expr_467_);
lean_dec_ref(v_x_445_);
v___x_468_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2);
v___x_469_ = l_Lean_mkAppB(v___x_468_, v_a_465_, v_expr_467_);
v___x_470_ = l_Lean_Meta_Sym_shareCommonInc(v___x_469_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
lean_inc(v_a_457_);
lean_inc_ref(v_a_456_);
lean_inc(v_a_455_);
lean_inc_ref(v_a_454_);
lean_inc(v_a_453_);
lean_inc_ref(v_a_452_);
lean_inc(v_a_451_);
lean_inc_ref(v_a_450_);
lean_inc(v_a_449_);
lean_inc(v_a_448_);
lean_inc_ref(v_a_447_);
v___x_472_ = lean_apply_12(v_satAtAtoms_466_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, lean_box(0));
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_483_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_483_ == 0)
{
v___x_475_ = v___x_472_;
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_472_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_483_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v___x_477_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6);
v___x_478_ = l_Lean_Expr_app___override(v_h_446_, v_a_465_);
v___x_479_ = l_Lean_mkApp3(v___x_477_, v_a_471_, v_a_473_, v___x_478_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 0, v___x_479_);
v___x_481_ = v___x_475_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_dec(v_a_471_);
lean_dec(v_a_465_);
lean_dec_ref(v_h_446_);
return v___x_472_;
}
}
else
{
lean_dec_ref(v_satAtAtoms_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_h_446_);
return v___x_470_;
}
}
else
{
lean_dec_ref(v_h_446_);
lean_dec_ref(v_x_445_);
return v___x_464_;
}
}
else
{
lean_object* v___x_484_; lean_object* v___x_485_; 
lean_dec_ref(v_h_446_);
lean_dec_ref(v_x_445_);
v___x_484_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8);
v___x_485_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v___x_484_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
return v___x_485_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_445_ = stack[0].m_obj;
lean_object* v_h_446_ = stack[1].m_obj;
lean_object* v_a_447_ = stack[2].m_obj;
lean_object* v_a_448_ = stack[3].m_obj;
lean_object* v_a_449_ = stack[4].m_obj;
lean_object* v_a_450_ = stack[5].m_obj;
lean_object* v_a_451_ = stack[6].m_obj;
lean_object* v_a_452_ = stack[7].m_obj;
lean_object* v_a_453_ = stack[8].m_obj;
lean_object* v_a_454_ = stack[9].m_obj;
lean_object* v_a_455_ = stack[10].m_obj;
lean_object* v_a_456_ = stack[11].m_obj;
lean_object* v_a_457_ = stack[12].m_obj;
lean_object* v_res_486_;
v_res_486_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_x_445_, v_h_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_);
stack->m_obj
 = v_res_486_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object* v_x_487_, lean_object* v_h_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_x_487_, v_h_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_);
lean_dec(v_a_499_);
lean_dec_ref(v_a_498_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
lean_dec(v_a_493_);
lean_dec_ref(v_a_492_);
lean_dec(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
return v_res_501_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(lean_object* v_00_u03b1_502_, lean_object* v_msg_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_503_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_516_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_503_ = stack[1].m_obj;
lean_object* v___y_504_ = stack[2].m_obj;
lean_object* v___y_505_ = stack[3].m_obj;
lean_object* v___y_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v___y_509_ = stack[7].m_obj;
lean_object* v___y_510_ = stack[8].m_obj;
lean_object* v___y_511_ = stack[9].m_obj;
lean_object* v___y_512_ = stack[10].m_obj;
lean_object* v___y_513_ = stack[11].m_obj;
lean_object* v___y_514_ = stack[12].m_obj;
lean_object* v_res_517_;
v_res_517_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(lean_box(0), v_msg_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object* v_00_u03b1_518_, lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(v_00_u03b1_518_, v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_532_;
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

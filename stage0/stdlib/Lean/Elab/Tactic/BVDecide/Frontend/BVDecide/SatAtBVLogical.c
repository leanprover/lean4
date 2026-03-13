// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.SatAtBVLogical
// Imports: public import Lean.Elab.Tactic.BVDecide.Frontend.BVDecide.Reify
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkRefl(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "BVLogicalExpr"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sat_and"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 227, 201, 30, 146, 23, 177, 97)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BoolExpr"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gate"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 48, 52, 229, 233, 139, 247, 222)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__4_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Gate"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__7_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__8_value),LEAN_SCALAR_PTR_LITERAL(191, 125, 195, 121, 220, 103, 239, 120)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 172, 123, 74, 237, 247, 157, 191)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__2;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "false_of_eq_true_of_eq_false"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 92, 17, 213, 68, 211, 219, 250)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 74, 55, 212, 47, 213, 221, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(214, 107, 11, 53, 155, 200, 122, 195)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Unable to identify any relevant atoms."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
if (v___x_4_ == 0)
{
lean_object* v___x_5_; 
v___x_5_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5_, 0, v_e_1_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v_mctx_7_; lean_object* v___x_8_; lean_object* v_fst_9_; lean_object* v_snd_10_; lean_object* v___x_11_; lean_object* v_cache_12_; lean_object* v_zetaDeltaFVarIds_13_; lean_object* v_postponed_14_; lean_object* v_diag_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_24_; 
v___x_6_ = lean_st_ref_get(v___y_2_);
v_mctx_7_ = lean_ctor_get(v___x_6_, 0);
lean_inc_ref(v_mctx_7_);
lean_dec(v___x_6_);
v___x_8_ = l_Lean_instantiateMVarsCore(v_mctx_7_, v_e_1_);
v_fst_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_fst_9_);
v_snd_10_ = lean_ctor_get(v___x_8_, 1);
lean_inc(v_snd_10_);
lean_dec_ref(v___x_8_);
v___x_11_ = lean_st_ref_take(v___y_2_);
v_cache_12_ = lean_ctor_get(v___x_11_, 1);
v_zetaDeltaFVarIds_13_ = lean_ctor_get(v___x_11_, 2);
v_postponed_14_ = lean_ctor_get(v___x_11_, 3);
v_diag_15_ = lean_ctor_get(v___x_11_, 4);
v_isSharedCheck_24_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_24_ == 0)
{
lean_object* v_unused_25_; 
v_unused_25_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_25_);
v___x_17_ = v___x_11_;
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_diag_15_);
lean_inc(v_postponed_14_);
lean_inc(v_zetaDeltaFVarIds_13_);
lean_inc(v_cache_12_);
lean_dec(v___x_11_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_24_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_20_; 
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_snd_10_);
v___x_20_ = v___x_17_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v_snd_10_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_cache_12_);
lean_ctor_set(v_reuseFailAlloc_23_, 2, v_zetaDeltaFVarIds_13_);
lean_ctor_set(v_reuseFailAlloc_23_, 3, v_postponed_14_);
lean_ctor_set(v_reuseFailAlloc_23_, 4, v_diag_15_);
v___x_20_ = v_reuseFailAlloc_23_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_st_ref_set(v___y_2_, v___x_20_);
v___x_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_22_, 0, v_fst_9_);
return v___x_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___redArg(v_e_30_, v___y_34_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_);
lean_dec(v___y_45_);
lean_dec_ref(v___y_44_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec(v___y_40_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___lam__0(lean_object* v_expr_48_, lean_object* v_val_49_, lean_object* v___x_50_, lean_object* v_arg_51_, lean_object* v_h_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v___x_59_; 
lean_inc(v___y_57_);
lean_inc_ref(v___y_56_);
lean_inc(v___y_55_);
lean_inc_ref(v___y_54_);
v___x_59_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkEvalExpr(v_expr_48_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_59_) == 0)
{
lean_object* v_a_60_; lean_object* v___x_61_; 
v_a_60_ = lean_ctor_get(v___x_59_, 0);
lean_inc(v_a_60_);
lean_dec_ref(v___x_59_);
v___x_61_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_evalsAtAtoms(v_val_49_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_76_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_76_ == 0)
{
v___x_64_ = v___x_61_;
v_isShared_65_ = v_isSharedCheck_76_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_61_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_76_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___y_67_; 
if (lean_obj_tag(v_a_62_) == 0)
{
lean_object* v___x_74_; 
lean_inc(v_a_60_);
v___x_74_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkRefl(v_a_60_);
v___y_67_ = v___x_74_;
goto v___jp_66_;
}
else
{
lean_object* v_val_75_; 
v_val_75_ = lean_ctor_get(v_a_62_, 0);
lean_inc(v_val_75_);
lean_dec_ref(v_a_62_);
v___y_67_ = v_val_75_;
goto v___jp_66_;
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_68_ = lean_box(0);
v___x_69_ = l_Lean_mkConst(v___x_50_, v___x_68_);
v___x_70_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_mkTrans(v_a_60_, v_arg_51_, v___x_69_, v___y_67_, v_h_52_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_70_);
v___x_72_ = v___x_64_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v_a_60_);
lean_dec_ref(v_h_52_);
lean_dec_ref(v_arg_51_);
lean_dec(v___x_50_);
v_a_77_ = lean_ctor_get(v___x_61_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_61_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_61_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_61_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
else
{
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v_h_52_);
lean_dec_ref(v_arg_51_);
lean_dec(v___x_50_);
lean_dec_ref(v_val_49_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___lam__0___boxed(lean_object* v_expr_85_, lean_object* v_val_86_, lean_object* v___x_87_, lean_object* v_arg_88_, lean_object* v_h_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___lam__0(v_expr_85_, v_val_86_, v___x_87_, v_arg_88_, v_h_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of(lean_object* v_h_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; 
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
lean_inc_ref(v_a_110_);
lean_inc_ref(v_h_107_);
v___x_115_ = lean_infer_type(v_h_107_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref(v___x_115_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
lean_inc_ref(v_a_110_);
v___x_117_ = l_Lean_Meta_whnfR(v_a_116_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_117_) == 0)
{
lean_object* v_a_118_; lean_object* v___x_119_; lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_202_; 
v_a_118_ = lean_ctor_get(v___x_117_, 0);
lean_inc(v_a_118_);
lean_dec_ref(v___x_117_);
v___x_119_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of_spec__0___redArg(v_a_118_, v_a_111_);
v_a_120_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_202_ == 0)
{
v___x_122_ = v___x_119_;
v_isShared_123_ = v_isSharedCheck_202_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_119_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_202_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; 
v___x_124_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_120_, v_a_111_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_193_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_193_ == 0)
{
v___x_127_ = v___x_124_;
v_isShared_128_ = v_isSharedCheck_193_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_193_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = l_Lean_Expr_cleanupAnnotations(v_a_125_);
v___x_135_ = l_Lean_Expr_isApp(v___x_134_);
if (v___x_135_ == 0)
{
lean_dec_ref(v___x_134_);
lean_del_object(v___x_122_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
goto v___jp_129_;
}
else
{
lean_object* v_arg_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_arg_136_ = lean_ctor_get(v___x_134_, 1);
lean_inc_ref(v_arg_136_);
v___x_137_ = l_Lean_Expr_appFnCleanup___redArg(v___x_134_);
v___x_138_ = l_Lean_Expr_isApp(v___x_137_);
if (v___x_138_ == 0)
{
lean_dec_ref(v___x_137_);
lean_dec_ref(v_arg_136_);
lean_del_object(v___x_122_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
goto v___jp_129_;
}
else
{
lean_object* v_arg_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_arg_139_ = lean_ctor_get(v___x_137_, 1);
lean_inc_ref(v_arg_139_);
v___x_140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_137_);
v___x_141_ = l_Lean_Expr_isApp(v___x_140_);
if (v___x_141_ == 0)
{
lean_dec_ref(v___x_140_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_136_);
lean_del_object(v___x_122_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
goto v___jp_129_;
}
else
{
lean_object* v_arg_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v_arg_142_ = lean_ctor_get(v___x_140_, 1);
lean_inc_ref(v_arg_142_);
v___x_143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_140_);
v___x_144_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__1));
v___x_145_ = l_Lean_Expr_isConstOf(v___x_143_, v___x_144_);
lean_dec_ref(v___x_143_);
if (v___x_145_ == 0)
{
lean_dec_ref(v_arg_142_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_136_);
lean_del_object(v___x_122_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
goto v___jp_129_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
lean_del_object(v___x_127_);
v___x_146_ = l_Lean_Expr_cleanupAnnotations(v_arg_142_);
v___x_147_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__3));
v___x_148_ = l_Lean_Expr_isConstOf(v___x_146_, v___x_147_);
lean_dec_ref(v___x_146_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v___x_151_; 
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_136_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
v___x_149_ = lean_box(0);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_149_);
v___x_151_ = v___x_122_;
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
else
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = l_Lean_Expr_cleanupAnnotations(v_arg_136_);
v___x_154_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___closed__5));
v___x_155_ = l_Lean_Expr_isConstOf(v___x_153_, v___x_154_);
lean_dec_ref(v___x_153_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_158_; 
lean_dec_ref(v_arg_139_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
v___x_156_ = lean_box(0);
if (v_isShared_123_ == 0)
{
lean_ctor_set(v___x_122_, 0, v___x_156_);
v___x_158_ = v___x_122_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
else
{
lean_object* v___x_160_; 
lean_del_object(v___x_122_);
lean_inc_ref(v_arg_139_);
v___x_160_ = l_Lean_Elab_Tactic_BVDecide_Frontend_ReifiedBVLogical_of(v_arg_139_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_184_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_184_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_184_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_184_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
if (lean_obj_tag(v_a_161_) == 1)
{
lean_object* v_val_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_179_; 
v_val_165_ = lean_ctor_get(v_a_161_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v_a_161_);
if (v_isSharedCheck_179_ == 0)
{
v___x_167_ = v_a_161_;
v_isShared_168_ = v_isSharedCheck_179_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_val_165_);
lean_dec(v_a_161_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_179_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v_bvExpr_169_; lean_object* v_expr_170_; lean_object* v___f_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v_bvExpr_169_ = lean_ctor_get(v_val_165_, 0);
lean_inc_ref(v_bvExpr_169_);
v_expr_170_ = lean_ctor_get(v_val_165_, 3);
lean_inc_ref(v_expr_170_);
lean_inc_ref(v_expr_170_);
v___f_171_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___lam__0___boxed), 11, 5);
lean_closure_set(v___f_171_, 0, v_expr_170_);
lean_closure_set(v___f_171_, 1, v_val_165_);
lean_closure_set(v___f_171_, 2, v___x_154_);
lean_closure_set(v___f_171_, 3, v_arg_139_);
lean_closure_set(v___f_171_, 4, v_h_107_);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v_bvExpr_169_);
lean_ctor_set(v___x_172_, 1, v___f_171_);
lean_ctor_set(v___x_172_, 2, v_expr_170_);
if (v_isShared_168_ == 0)
{
lean_ctor_set(v___x_167_, 0, v___x_172_);
v___x_174_ = v___x_167_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_174_);
v___x_176_ = v___x_163_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v___x_180_; lean_object* v___x_182_; 
lean_dec(v_a_161_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_h_107_);
v___x_180_ = lean_box(0);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_180_);
v___x_182_ = v___x_163_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_h_107_);
v_a_185_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_160_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_160_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
}
}
}
}
}
v___jp_129_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_130_ = lean_box(0);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 0, v___x_130_);
v___x_132_ = v___x_127_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
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
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_del_object(v___x_122_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
v_a_194_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_124_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_124_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
v_a_203_ = lean_ctor_get(v___x_117_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_117_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_117_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec(v_a_111_);
lean_dec_ref(v_a_110_);
lean_dec(v_a_109_);
lean_dec_ref(v_h_107_);
v_a_211_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_115_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_115_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of___boxed(lean_object* v_h_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_of(v_h_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_220_);
return v_res_227_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__6(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_239_ = lean_box(0);
v___x_240_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__5));
v___x_241_ = l_Lean_mkConst(v___x_240_, v___x_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0(lean_object* v_satAtAtoms_242_, lean_object* v_satAtAtoms_243_, lean_object* v_expr_244_, lean_object* v_expr_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; 
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
v___x_252_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_254_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v___x_252_);
lean_inc(v___y_250_);
lean_inc_ref(v___y_249_);
lean_inc(v___y_248_);
lean_inc_ref(v___y_247_);
lean_inc(v___y_246_);
v___x_254_ = lean_apply_6(v_satAtAtoms_242_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, lean_box(0));
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_256_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref(v___x_254_);
v___x_256_ = lean_apply_6(v_satAtAtoms_243_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, lean_box(0));
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_266_; 
v_a_257_ = lean_ctor_get(v___x_256_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_256_);
if (v_isSharedCheck_266_ == 0)
{
v___x_259_ = v___x_256_;
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_256_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_266_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_261_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___closed__6);
v___x_262_ = l_Lean_mkApp5(v___x_261_, v_expr_244_, v_expr_245_, v_a_253_, v_a_255_, v_a_257_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_262_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_dec(v_a_255_);
lean_dec(v_a_253_);
lean_dec_ref(v_expr_245_);
lean_dec_ref(v_expr_244_);
return v___x_256_;
}
}
else
{
lean_dec(v_a_253_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v_expr_245_);
lean_dec_ref(v_expr_244_);
lean_dec_ref(v_satAtAtoms_243_);
return v___x_254_;
}
}
else
{
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v_expr_245_);
lean_dec_ref(v_expr_244_);
lean_dec_ref(v_satAtAtoms_243_);
lean_dec_ref(v_satAtAtoms_242_);
return v___x_252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___boxed(lean_object* v_satAtAtoms_267_, lean_object* v_satAtAtoms_268_, lean_object* v_expr_269_, lean_object* v_expr_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0(v_satAtAtoms_267_, v_satAtAtoms_268_, v_expr_269_, v_expr_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
return v_res_277_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__3(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_box(0);
v___x_287_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__2));
v___x_288_ = l_Lean_mkConst(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__6(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_box(0);
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__5));
v___x_297_ = l_Lean_mkConst(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__10(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_box(0);
v___x_307_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__9));
v___x_308_ = l_Lean_mkConst(v___x_307_, v___x_306_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and(lean_object* v_x_309_, lean_object* v_y_310_){
_start:
{
lean_object* v_bvExpr_311_; lean_object* v_satAtAtoms_312_; lean_object* v_expr_313_; lean_object* v_bvExpr_314_; lean_object* v_satAtAtoms_315_; lean_object* v_expr_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_330_; 
v_bvExpr_311_ = lean_ctor_get(v_x_309_, 0);
lean_inc_ref(v_bvExpr_311_);
v_satAtAtoms_312_ = lean_ctor_get(v_x_309_, 1);
lean_inc_ref(v_satAtAtoms_312_);
v_expr_313_ = lean_ctor_get(v_x_309_, 2);
lean_inc_ref(v_expr_313_);
lean_dec_ref(v_x_309_);
v_bvExpr_314_ = lean_ctor_get(v_y_310_, 0);
v_satAtAtoms_315_ = lean_ctor_get(v_y_310_, 1);
v_expr_316_ = lean_ctor_get(v_y_310_, 2);
v_isSharedCheck_330_ = !lean_is_exclusive(v_y_310_);
if (v_isSharedCheck_330_ == 0)
{
v___x_318_ = v_y_310_;
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_expr_316_);
lean_inc(v_satAtAtoms_315_);
lean_inc(v_bvExpr_314_);
lean_dec(v_y_310_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_330_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; lean_object* v___f_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_320_ = 0;
lean_inc_ref(v_expr_316_);
lean_inc_ref(v_expr_313_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___lam__0___boxed), 10, 4);
lean_closure_set(v___f_321_, 0, v_satAtAtoms_312_);
lean_closure_set(v___f_321_, 1, v_satAtAtoms_315_);
lean_closure_set(v___f_321_, 2, v_expr_313_);
lean_closure_set(v___f_321_, 3, v_expr_316_);
v___x_322_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_322_, 0, v_bvExpr_311_);
lean_ctor_set(v___x_322_, 1, v_bvExpr_314_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*2, v___x_320_);
v___x_323_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__3);
v___x_324_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__6);
v___x_325_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__10, &l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__10_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_and___closed__10);
v___x_326_ = l_Lean_mkApp4(v___x_323_, v___x_324_, v___x_325_, v_expr_313_, v_expr_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 2, v___x_326_);
lean_ctor_set(v___x_318_, 1, v___f_321_);
lean_ctor_set(v___x_318_, 0, v___x_322_);
v___x_328_ = v___x_318_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___f_321_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___x_326_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0_spec__0(lean_object* v_msgData_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_env_338_; lean_object* v___x_339_; lean_object* v_mctx_340_; lean_object* v_lctx_341_; lean_object* v_options_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_337_ = lean_st_ref_get(v___y_335_);
v_env_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_env_338_);
lean_dec(v___x_337_);
v___x_339_ = lean_st_ref_get(v___y_333_);
v_mctx_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc_ref(v_mctx_340_);
lean_dec(v___x_339_);
v_lctx_341_ = lean_ctor_get(v___y_332_, 2);
v_options_342_ = lean_ctor_get(v___y_334_, 2);
lean_inc_ref(v_options_342_);
lean_inc_ref(v_lctx_341_);
v___x_343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_343_, 0, v_env_338_);
lean_ctor_set(v___x_343_, 1, v_mctx_340_);
lean_ctor_set(v___x_343_, 2, v_lctx_341_);
lean_ctor_set(v___x_343_, 3, v_options_342_);
v___x_344_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_msgData_331_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msgData_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___redArg(lean_object* v_msg_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_ref_359_; lean_object* v___x_360_; lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_369_; 
v_ref_359_ = lean_ctor_get(v___y_356_, 5);
v___x_360_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msg_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
v_a_361_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_369_ == 0)
{
v___x_363_ = v___x_360_;
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_369_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
lean_inc(v_ref_359_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v_ref_359_);
lean_ctor_set(v___x_365_, 1, v_a_361_);
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 1);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(lean_object* v_msg_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
return v_res_376_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_384_ = lean_box(0);
v___x_385_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__1));
v___x_386_ = l_Lean_mkConst(v___x_385_, v___x_384_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_box(0);
v___x_397_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__5));
v___x_398_ = l_Lean_mkConst(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__8(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__7));
v___x_401_ = l_Lean_stringToMessageData(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse(lean_object* v_x_402_, lean_object* v_h_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_atoms_411_; lean_object* v_size_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_410_ = lean_st_ref_get(v_a_404_);
v_atoms_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc_ref(v_atoms_411_);
lean_dec(v___x_410_);
v_size_412_ = lean_ctor_get(v_atoms_411_, 0);
lean_inc(v_size_412_);
lean_dec_ref(v_atoms_411_);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_nat_dec_eq(v_size_412_, v___x_413_);
lean_dec(v_size_412_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_inc(v_a_408_);
lean_inc_ref(v_a_407_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
v___x_415_ = l_Lean_Elab_Tactic_BVDecide_Frontend_M_atomsAssignment(v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_a_416_; lean_object* v_satAtAtoms_417_; lean_object* v_expr_418_; lean_object* v___x_419_; 
v_a_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_a_416_);
lean_dec_ref(v___x_415_);
v_satAtAtoms_417_ = lean_ctor_get(v_x_402_, 1);
lean_inc_ref(v_satAtAtoms_417_);
v_expr_418_ = lean_ctor_get(v_x_402_, 2);
lean_inc_ref(v_expr_418_);
lean_dec_ref(v_x_402_);
v___x_419_ = lean_apply_6(v_satAtAtoms_417_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, lean_box(0));
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_432_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_432_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_432_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_432_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_424_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__2, &l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__2_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__2);
lean_inc(v_a_416_);
v___x_425_ = l_Lean_mkAppB(v___x_424_, v_a_416_, v_expr_418_);
v___x_426_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__6, &l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__6_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__6);
v___x_427_ = l_Lean_Expr_app___override(v_h_403_, v_a_416_);
v___x_428_ = l_Lean_mkApp3(v___x_426_, v___x_425_, v_a_420_, v___x_427_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_428_);
v___x_430_ = v___x_422_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
else
{
lean_dec_ref(v_expr_418_);
lean_dec(v_a_416_);
lean_dec_ref(v_h_403_);
return v___x_419_;
}
}
else
{
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_h_403_);
lean_dec_ref(v_x_402_);
return v___x_415_;
}
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_a_404_);
lean_dec_ref(v_h_403_);
lean_dec_ref(v_x_402_);
v___x_433_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___closed__8);
v___x_434_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___redArg(v___x_433_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse___boxed(lean_object* v_x_435_, lean_object* v_h_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse(v_x_435_, v_h_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0(lean_object* v_00_u03b1_444_, lean_object* v_msg_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_445_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object* v_00_u03b1_453_, lean_object* v_msg_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_SatAtBVLogical_proveFalse_spec__0(v_00_u03b1_453_, v_msg_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
return v_res_461_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_BVDecide_SatAtBVLogical(builtin);
}
#ifdef __cplusplus
}
#endif

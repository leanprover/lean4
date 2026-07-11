// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.SatAtBVLogical
// Imports: public import Lean.Meta.Tactic.BVDecide.Reflect.Reify
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "BVLogicalExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sat_and"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 227, 201, 30, 146, 23, 177, 97)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BoolExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__1_value),LEAN_SCALAR_PTR_LITERAL(65, 48, 52, 229, 233, 139, 247, 222)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__4_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__7_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__8_value),LEAN_SCALAR_PTR_LITERAL(191, 125, 195, 121, 220, 103, 239, 120)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "eval"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(170, 137, 185, 0, 130, 201, 136, 210)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 172, 123, 74, 237, 247, 157, 191)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Reflect"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "false_of_eq_true_of_eq_false"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
_start:
{
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(v_e_31_, v___y_35_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___boxed(lean_object* v_e_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0(v_e_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_);
lean_dec(v___y_46_);
lean_dec_ref(v___y_45_);
lean_dec(v___y_44_);
lean_dec_ref(v___y_43_);
lean_dec(v___y_42_);
lean_dec(v___y_41_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(lean_object* v_expr_49_, lean_object* v_val_50_, lean_object* v___x_51_, lean_object* v_arg_52_, lean_object* v_h_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkEvalExpr(v_expr_49_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_62_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v___x_60_, 1);
v___x_62_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_val_50_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_77_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_77_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_77_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_77_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_77_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___y_68_; 
if (lean_obj_tag(v_a_63_) == 0)
{
lean_object* v___x_75_; 
lean_inc(v_a_61_);
v___x_75_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkRefl(v_a_61_);
v___y_68_ = v___x_75_;
goto v___jp_67_;
}
else
{
lean_object* v_val_76_; 
v_val_76_ = lean_ctor_get(v_a_63_, 0);
lean_inc(v_val_76_);
lean_dec_ref_known(v_a_63_, 1);
v___y_68_ = v_val_76_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_69_ = lean_box(0);
v___x_70_ = l_Lean_mkConst(v___x_51_, v___x_69_);
v___x_71_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_mkTrans(v_a_61_, v_arg_52_, v___x_70_, v___y_68_, v_h_53_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_71_);
v___x_73_ = v___x_65_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_dec(v_a_61_);
lean_dec_ref(v_h_53_);
lean_dec_ref(v_arg_52_);
lean_dec(v___x_51_);
v_a_78_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_62_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_62_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
else
{
lean_dec_ref(v_h_53_);
lean_dec_ref(v_arg_52_);
lean_dec(v___x_51_);
lean_dec_ref(v_val_50_);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed(lean_object* v_expr_86_, lean_object* v_val_87_, lean_object* v___x_88_, lean_object* v_arg_89_, lean_object* v_h_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0(v_expr_86_, v_val_87_, v___x_88_, v_arg_89_, v_h_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
lean_dec(v___y_91_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(lean_object* v_h_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
lean_inc(v_a_114_);
lean_inc_ref(v_a_113_);
lean_inc(v_a_112_);
lean_inc_ref(v_a_111_);
lean_inc_ref(v_h_108_);
v___x_116_ = lean_infer_type(v_h_108_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = l_Lean_Meta_whnfR(v_a_117_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_203_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = l_Lean_instantiateMVars___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of_spec__0___redArg(v_a_119_, v_a_112_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_203_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_203_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_203_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_a_121_, v_a_112_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_194_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_194_ == 0)
{
v___x_128_ = v___x_125_;
v_isShared_129_ = v_isSharedCheck_194_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_125_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_194_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = l_Lean_Expr_cleanupAnnotations(v_a_126_);
v___x_136_ = l_Lean_Expr_isApp(v___x_135_);
if (v___x_136_ == 0)
{
lean_dec_ref(v___x_135_);
lean_del_object(v___x_123_);
lean_dec_ref(v_h_108_);
goto v___jp_130_;
}
else
{
lean_object* v_arg_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_arg_137_ = lean_ctor_get(v___x_135_, 1);
lean_inc_ref(v_arg_137_);
v___x_138_ = l_Lean_Expr_appFnCleanup___redArg(v___x_135_);
v___x_139_ = l_Lean_Expr_isApp(v___x_138_);
if (v___x_139_ == 0)
{
lean_dec_ref(v___x_138_);
lean_dec_ref(v_arg_137_);
lean_del_object(v___x_123_);
lean_dec_ref(v_h_108_);
goto v___jp_130_;
}
else
{
lean_object* v_arg_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_arg_140_ = lean_ctor_get(v___x_138_, 1);
lean_inc_ref(v_arg_140_);
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_138_);
v___x_142_ = l_Lean_Expr_isApp(v___x_141_);
if (v___x_142_ == 0)
{
lean_dec_ref(v___x_141_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_137_);
lean_del_object(v___x_123_);
lean_dec_ref(v_h_108_);
goto v___jp_130_;
}
else
{
lean_object* v_arg_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_arg_143_ = lean_ctor_get(v___x_141_, 1);
lean_inc_ref(v_arg_143_);
v___x_144_ = l_Lean_Expr_appFnCleanup___redArg(v___x_141_);
v___x_145_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__1));
v___x_146_ = l_Lean_Expr_isConstOf(v___x_144_, v___x_145_);
lean_dec_ref(v___x_144_);
if (v___x_146_ == 0)
{
lean_dec_ref(v_arg_143_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_137_);
lean_del_object(v___x_123_);
lean_dec_ref(v_h_108_);
goto v___jp_130_;
}
else
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
lean_del_object(v___x_128_);
v___x_147_ = l_Lean_Expr_cleanupAnnotations(v_arg_143_);
v___x_148_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__3));
v___x_149_ = l_Lean_Expr_isConstOf(v___x_147_, v___x_148_);
lean_dec_ref(v___x_147_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_152_; 
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_137_);
lean_dec_ref(v_h_108_);
v___x_150_ = lean_box(0);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_150_);
v___x_152_ = v___x_123_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = l_Lean_Expr_cleanupAnnotations(v_arg_137_);
v___x_155_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___closed__5));
v___x_156_ = l_Lean_Expr_isConstOf(v___x_154_, v___x_155_);
lean_dec_ref(v___x_154_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_h_108_);
v___x_157_ = lean_box(0);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 0, v___x_157_);
v___x_159_ = v___x_123_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
else
{
lean_object* v___x_161_; 
lean_del_object(v___x_123_);
lean_inc_ref(v_arg_140_);
v___x_161_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_of(v_arg_140_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_185_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_185_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_185_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_185_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
if (lean_obj_tag(v_a_162_) == 1)
{
lean_object* v_val_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_180_; 
v_val_166_ = lean_ctor_get(v_a_162_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v_a_162_);
if (v_isSharedCheck_180_ == 0)
{
v___x_168_ = v_a_162_;
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_val_166_);
lean_dec(v_a_162_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_180_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_bvExpr_170_; lean_object* v_expr_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
v_bvExpr_170_ = lean_ctor_get(v_val_166_, 0);
lean_inc_ref(v_bvExpr_170_);
v_expr_171_ = lean_ctor_get(v_val_166_, 3);
lean_inc_ref_n(v_expr_171_, 2);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___lam__0___boxed), 11, 5);
lean_closure_set(v___f_172_, 0, v_expr_171_);
lean_closure_set(v___f_172_, 1, v_val_166_);
lean_closure_set(v___f_172_, 2, v___x_155_);
lean_closure_set(v___f_172_, 3, v_arg_140_);
lean_closure_set(v___f_172_, 4, v_h_108_);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v_bvExpr_170_);
lean_ctor_set(v___x_173_, 1, v___f_172_);
lean_ctor_set(v___x_173_, 2, v_expr_171_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_173_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v___x_173_);
v___x_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_175_);
v___x_177_ = v___x_164_;
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
lean_dec(v_a_162_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_h_108_);
v___x_181_ = lean_box(0);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_181_);
v___x_183_ = v___x_164_;
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
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_h_108_);
v_a_186_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_161_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_161_);
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
}
}
}
v___jp_130_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_box(0);
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v___x_131_);
v___x_133_ = v___x_128_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
else
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
lean_del_object(v___x_123_);
lean_dec_ref(v_h_108_);
v_a_195_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_125_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_125_);
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
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec_ref(v_h_108_);
v_a_204_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_118_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_118_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec_ref(v_h_108_);
v_a_212_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_116_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_116_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of___boxed(lean_object* v_h_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_of(v_h_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_a_221_);
return v_res_228_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_240_ = lean_box(0);
v___x_241_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__5));
v___x_242_ = l_Lean_mkConst(v___x_241_, v___x_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0(lean_object* v_satAtAtoms_243_, lean_object* v_satAtAtoms_244_, lean_object* v_expr_245_, lean_object* v_expr_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; lean_object* v___x_255_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
v___x_255_ = lean_apply_6(v_satAtAtoms_243_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, lean_box(0));
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v___x_255_, 1);
lean_inc(v___y_251_);
lean_inc_ref(v___y_250_);
lean_inc(v___y_249_);
lean_inc_ref(v___y_248_);
lean_inc(v___y_247_);
v___x_257_ = lean_apply_6(v_satAtAtoms_244_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, lean_box(0));
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_267_; 
v_a_258_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_267_ == 0)
{
v___x_260_ = v___x_257_;
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_257_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_267_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_262_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___closed__6);
v___x_263_ = l_Lean_mkApp5(v___x_262_, v_expr_245_, v_expr_246_, v_a_254_, v_a_256_, v_a_258_);
if (v_isShared_261_ == 0)
{
lean_ctor_set(v___x_260_, 0, v___x_263_);
v___x_265_ = v___x_260_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_263_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
else
{
lean_dec(v_a_256_);
lean_dec(v_a_254_);
lean_dec_ref(v_expr_246_);
lean_dec_ref(v_expr_245_);
return v___x_257_;
}
}
else
{
lean_dec(v_a_254_);
lean_dec_ref(v_expr_246_);
lean_dec_ref(v_expr_245_);
lean_dec_ref(v_satAtAtoms_244_);
return v___x_255_;
}
}
else
{
lean_dec_ref(v_expr_246_);
lean_dec_ref(v_expr_245_);
lean_dec_ref(v_satAtAtoms_244_);
lean_dec_ref(v_satAtAtoms_243_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___boxed(lean_object* v_satAtAtoms_268_, lean_object* v_satAtAtoms_269_, lean_object* v_expr_270_, lean_object* v_expr_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0(v_satAtAtoms_268_, v_satAtAtoms_269_, v_expr_270_, v_expr_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
return v_res_278_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_box(0);
v___x_288_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__2));
v___x_289_ = l_Lean_mkConst(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_box(0);
v___x_297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__5));
v___x_298_ = l_Lean_mkConst(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_box(0);
v___x_308_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__9));
v___x_309_ = l_Lean_mkConst(v___x_308_, v___x_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and(lean_object* v_x_310_, lean_object* v_y_311_){
_start:
{
lean_object* v_bvExpr_312_; lean_object* v_satAtAtoms_313_; lean_object* v_expr_314_; lean_object* v_bvExpr_315_; lean_object* v_satAtAtoms_316_; lean_object* v_expr_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_331_; 
v_bvExpr_312_ = lean_ctor_get(v_x_310_, 0);
lean_inc_ref(v_bvExpr_312_);
v_satAtAtoms_313_ = lean_ctor_get(v_x_310_, 1);
lean_inc_ref(v_satAtAtoms_313_);
v_expr_314_ = lean_ctor_get(v_x_310_, 2);
lean_inc_ref(v_expr_314_);
lean_dec_ref(v_x_310_);
v_bvExpr_315_ = lean_ctor_get(v_y_311_, 0);
v_satAtAtoms_316_ = lean_ctor_get(v_y_311_, 1);
v_expr_317_ = lean_ctor_get(v_y_311_, 2);
v_isSharedCheck_331_ = !lean_is_exclusive(v_y_311_);
if (v_isSharedCheck_331_ == 0)
{
v___x_319_ = v_y_311_;
v_isShared_320_ = v_isSharedCheck_331_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_expr_317_);
lean_inc(v_satAtAtoms_316_);
lean_inc(v_bvExpr_315_);
lean_dec(v_y_311_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_331_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___x_321_; lean_object* v___f_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_321_ = 0;
lean_inc_ref(v_expr_317_);
lean_inc_ref(v_expr_314_);
v___f_322_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___lam__0___boxed), 10, 4);
lean_closure_set(v___f_322_, 0, v_satAtAtoms_313_);
lean_closure_set(v___f_322_, 1, v_satAtAtoms_316_);
lean_closure_set(v___f_322_, 2, v_expr_314_);
lean_closure_set(v___f_322_, 3, v_expr_317_);
v___x_323_ = lean_alloc_ctor(3, 2, 1);
lean_ctor_set(v___x_323_, 0, v_bvExpr_312_);
lean_ctor_set(v___x_323_, 1, v_bvExpr_315_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*2, v___x_321_);
v___x_324_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__3);
v___x_325_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__6);
v___x_326_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_and___closed__10);
v___x_327_ = l_Lean_mkApp4(v___x_324_, v___x_325_, v___x_326_, v_expr_314_, v_expr_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 2, v___x_327_);
lean_ctor_set(v___x_319_, 1, v___f_322_);
lean_ctor_set(v___x_319_, 0, v___x_323_);
v___x_329_ = v___x_319_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___f_322_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(lean_object* v_msgData_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_env_339_; lean_object* v___x_340_; lean_object* v_mctx_341_; lean_object* v_lctx_342_; lean_object* v_options_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_338_ = lean_st_ref_get(v___y_336_);
v_env_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_env_339_);
lean_dec(v___x_338_);
v___x_340_ = lean_st_ref_get(v___y_334_);
v_mctx_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc_ref(v_mctx_341_);
lean_dec(v___x_340_);
v_lctx_342_ = lean_ctor_get(v___y_333_, 2);
v_options_343_ = lean_ctor_get(v___y_335_, 2);
lean_inc_ref(v_options_343_);
lean_inc_ref(v_lctx_342_);
v___x_344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_344_, 0, v_env_339_);
lean_ctor_set(v___x_344_, 1, v_mctx_341_);
lean_ctor_set(v___x_344_, 2, v_lctx_342_);
lean_ctor_set(v___x_344_, 3, v_options_343_);
v___x_345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_msgData_332_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0___boxed(lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msgData_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(lean_object* v_msg_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_ref_360_; lean_object* v___x_361_; lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v_ref_360_ = lean_ctor_get(v___y_357_, 5);
v___x_361_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0_spec__0(v_msg_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_);
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_370_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
lean_inc(v_ref_360_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v_ref_360_);
lean_ctor_set(v___x_366_, 1, v_a_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set_tag(v___x_364_, 1);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg___boxed(lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_377_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = lean_box(0);
v___x_386_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__1));
v___x_387_ = l_Lean_mkConst(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_box(0);
v___x_398_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__5));
v___x_399_ = l_Lean_mkConst(v___x_398_, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8(void){
_start:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__7));
v___x_402_ = l_Lean_stringToMessageData(v___x_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(lean_object* v_x_403_, lean_object* v_h_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v_atoms_412_; lean_object* v_size_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_411_ = lean_st_ref_get(v_a_405_);
v_atoms_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_atoms_412_);
lean_dec(v___x_411_);
v_size_413_ = lean_ctor_get(v_atoms_412_, 0);
lean_inc(v_size_413_);
lean_dec_ref(v_atoms_412_);
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = lean_nat_dec_eq(v_size_413_, v___x_414_);
lean_dec(v_size_413_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
v___x_416_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; lean_object* v_satAtAtoms_418_; lean_object* v_expr_419_; lean_object* v___x_420_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
v_satAtAtoms_418_ = lean_ctor_get(v_x_403_, 1);
lean_inc_ref(v_satAtAtoms_418_);
v_expr_419_ = lean_ctor_get(v_x_403_, 2);
lean_inc_ref(v_expr_419_);
lean_dec_ref(v_x_403_);
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
lean_inc(v_a_407_);
lean_inc_ref(v_a_406_);
lean_inc(v_a_405_);
v___x_420_ = lean_apply_6(v_satAtAtoms_418_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, lean_box(0));
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_433_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_433_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_433_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_425_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__2);
lean_inc(v_a_417_);
v___x_426_ = l_Lean_mkAppB(v___x_425_, v_a_417_, v_expr_419_);
v___x_427_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__6);
v___x_428_ = l_Lean_Expr_app___override(v_h_404_, v_a_417_);
v___x_429_ = l_Lean_mkApp3(v___x_427_, v___x_426_, v_a_421_, v___x_428_);
if (v_isShared_424_ == 0)
{
lean_ctor_set(v___x_423_, 0, v___x_429_);
v___x_431_ = v___x_423_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
else
{
lean_dec_ref(v_expr_419_);
lean_dec(v_a_417_);
lean_dec_ref(v_h_404_);
return v___x_420_;
}
}
else
{
lean_dec_ref(v_h_404_);
lean_dec_ref(v_x_403_);
return v___x_416_;
}
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v_h_404_);
lean_dec_ref(v_x_403_);
v___x_434_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8, &l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8_once, _init_l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___closed__8);
v___x_435_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v___x_434_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse___boxed(lean_object* v_x_436_, lean_object* v_h_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse(v_x_436_, v_h_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(lean_object* v_00_u03b1_445_, lean_object* v_msg_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___redArg(v_msg_446_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0___boxed(lean_object* v_00_u03b1_454_, lean_object* v_msg_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_throwError___at___00Lean_Meta_Tactic_BVDecide_SatAtBVLogical_proveFalse_spec__0(v_00_u03b1_454_, v_msg_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
return v_res_462_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_SatAtBVLogical(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Reflect_Reify(builtin);
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

// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.ShortCircuit
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic public import Std.Tactic.BVDecide.Normalize.BitVec import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Sym.Simp.Rewrite
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
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "BEq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 188, 39, 55, 57, 152, 88, 223)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 52, 243, 194, 7, 226, 90, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__6_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__5_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__6_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__9_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__8_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__9_value),LEAN_SCALAR_PTR_LITERAL(208, 215, 171, 150, 192, 180, 249, 22)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__15_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__8_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__15_value),LEAN_SCALAR_PTR_LITERAL(160, 26, 8, 228, 104, 32, 82, 85)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__16_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Normalize"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "mul_beq_mul_short_circuit_left"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__20_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__21_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 181, 64, 73, 102, 44, 61, 193)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__22_value),LEAN_SCALAR_PTR_LITERAL(53, 48, 36, 136, 58, 30, 220, 150)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "mul_beq_mul_short_circuit_right"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__25_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__18_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__19_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__20_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__21_value),LEAN_SCALAR_PTR_LITERAL(105, 120, 51, 161, 199, 191, 75, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__3_value),LEAN_SCALAR_PTR_LITERAL(6, 181, 64, 73, 102, 44, 61, 193)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__25_value),LEAN_SCALAR_PTR_LITERAL(98, 146, 161, 224, 242, 166, 216, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__0_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "shortCircuitPass"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__2_value),LEAN_SCALAR_PTR_LITERAL(45, 197, 199, 240, 107, 41, 97, 28)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__3_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__1_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___closed__4_value;
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(lean_object* v_x_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___closed__0));
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3_ = stack[0].m_obj;
lean_object* v___y_4_ = stack[1].m_obj;
lean_object* v___y_5_ = stack[2].m_obj;
lean_object* v___y_6_ = stack[3].m_obj;
lean_object* v___y_7_ = stack[4].m_obj;
lean_object* v___y_8_ = stack[5].m_obj;
lean_object* v___y_9_ = stack[6].m_obj;
lean_object* v___y_10_ = stack[7].m_obj;
lean_object* v___y_11_ = stack[8].m_obj;
lean_object* v___y_12_ = stack[9].m_obj;
lean_object* v_res_16_;
v_res_16_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v_x_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, v___y_11_, v___y_12_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___boxed(lean_object* v_x_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v_x_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v___y_22_);
lean_dec_ref(v___y_21_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
return v_res_28_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_box(0);
v___x_48_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__10));
v___x_49_ = l_Lean_mkConst(v___x_48_, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = l_Lean_Level_ofNat(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
v___x_53_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12);
v___x_54_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13);
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2));
v___x_57_ = l_Lean_mkConst(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__16));
v___x_64_ = l_Lean_mkConst(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_box(0);
v___x_78_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23));
v___x_79_ = l_Lean_mkConst(v___x_78_, v___x_77_);
return v___x_79_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_box(0);
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26));
v___x_90_ = l_Lean_mkConst(v___x_89_, v___x_88_);
return v___x_90_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc(lean_object* v_e_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
uint8_t v_contextDependent_103_; lean_object* v_e_x27_108_; lean_object* v_proof_109_; uint8_t v_contextDependent_110_; lean_object* v___y_115_; lean_object* v___x_121_; uint8_t v___x_122_; 
lean_inc_ref(v_e_91_);
v___x_121_ = l_Lean_Expr_cleanupAnnotations(v_e_91_);
v___x_122_ = l_Lean_Expr_isApp(v___x_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v___x_124_; 
lean_dec_ref(v___x_121_);
lean_dec_ref(v_e_91_);
v___x_123_ = lean_box(0);
v___x_124_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_123_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_124_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v_arg_125_ = lean_ctor_get(v___x_121_, 1);
lean_inc_ref(v_arg_125_);
v___x_126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_121_);
v___x_127_ = l_Lean_Expr_isApp(v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec_ref(v___x_126_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_128_ = lean_box(0);
v___x_129_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_128_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_129_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v_arg_130_ = lean_ctor_get(v___x_126_, 1);
lean_inc_ref(v_arg_130_);
v___x_131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_126_);
v___x_132_ = l_Lean_Expr_isApp(v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref(v___x_131_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_133_ = lean_box(0);
v___x_134_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_133_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_134_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v_arg_135_ = lean_ctor_get(v___x_131_, 1);
lean_inc_ref(v_arg_135_);
v___x_136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_131_);
v___x_137_ = l_Lean_Expr_isApp(v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec_ref(v___x_136_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_138_ = lean_box(0);
v___x_139_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_138_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_139_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_arg_140_ = lean_ctor_get(v___x_136_, 1);
lean_inc_ref(v_arg_140_);
v___x_141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_136_);
v___x_142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2));
v___x_143_ = l_Lean_Expr_isConstOf(v___x_141_, v___x_142_);
lean_dec_ref(v___x_141_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_144_ = lean_box(0);
v___x_145_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_144_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_145_;
goto v___jp_114_;
}
else
{
lean_object* v___x_146_; uint8_t v___x_147_; 
lean_inc_ref(v_arg_140_);
v___x_146_ = l_Lean_Expr_cleanupAnnotations(v_arg_140_);
v___x_147_ = l_Lean_Expr_isApp(v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec_ref(v___x_146_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_148_ = lean_box(0);
v___x_149_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_148_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_149_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v_arg_150_ = lean_ctor_get(v___x_146_, 1);
lean_inc_ref(v_arg_150_);
v___x_151_ = l_Lean_Expr_appFnCleanup___redArg(v___x_146_);
v___x_152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__4));
v___x_153_ = l_Lean_Expr_isConstOf(v___x_151_, v___x_152_);
lean_dec_ref(v___x_151_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_130_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_154_ = lean_box(0);
v___x_155_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_154_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_155_;
goto v___jp_114_;
}
else
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = l_Lean_Expr_cleanupAnnotations(v_arg_130_);
v___x_157_ = l_Lean_Expr_isApp(v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; 
lean_dec_ref(v___x_156_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_158_ = lean_box(0);
v___x_159_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_158_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_159_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_arg_160_ = lean_ctor_get(v___x_156_, 1);
lean_inc_ref(v_arg_160_);
v___x_161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_156_);
v___x_162_ = l_Lean_Expr_isApp(v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec_ref(v___x_161_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_163_ = lean_box(0);
v___x_164_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_163_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_164_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_arg_165_ = lean_ctor_get(v___x_161_, 1);
lean_inc_ref(v_arg_165_);
v___x_166_ = l_Lean_Expr_appFnCleanup___redArg(v___x_161_);
v___x_167_ = l_Lean_Expr_isApp(v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec_ref(v___x_166_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_168_ = lean_box(0);
v___x_169_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_168_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_169_;
goto v___jp_114_;
}
else
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = l_Lean_Expr_appFnCleanup___redArg(v___x_166_);
v___x_171_ = l_Lean_Expr_isApp(v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec_ref(v___x_170_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_172_ = lean_box(0);
v___x_173_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_172_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_173_;
goto v___jp_114_;
}
else
{
lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_170_);
v___x_175_ = l_Lean_Expr_isApp(v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; lean_object* v___x_177_; 
lean_dec_ref(v___x_174_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_176_ = lean_box(0);
v___x_177_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_176_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_177_;
goto v___jp_114_;
}
else
{
lean_object* v___x_178_; uint8_t v___x_179_; 
v___x_178_ = l_Lean_Expr_appFnCleanup___redArg(v___x_174_);
v___x_179_ = l_Lean_Expr_isApp(v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
lean_dec_ref(v___x_178_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_180_ = lean_box(0);
v___x_181_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_180_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_181_;
goto v___jp_114_;
}
else
{
lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_182_ = l_Lean_Expr_appFnCleanup___redArg(v___x_178_);
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__7));
v___x_184_ = l_Lean_Expr_isConstOf(v___x_182_, v___x_183_);
lean_dec_ref(v___x_182_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_arg_125_);
lean_dec_ref(v_e_91_);
v___x_185_ = lean_box(0);
v___x_186_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_185_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_186_;
goto v___jp_114_;
}
else
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = l_Lean_Expr_cleanupAnnotations(v_arg_125_);
v___x_188_ = l_Lean_Expr_isApp(v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec_ref(v___x_187_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v___x_189_ = lean_box(0);
v___x_190_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_189_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_190_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_arg_191_ = lean_ctor_get(v___x_187_, 1);
lean_inc_ref(v_arg_191_);
v___x_192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_187_);
v___x_193_ = l_Lean_Expr_isApp(v___x_192_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; 
lean_dec_ref(v___x_192_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v___x_194_ = lean_box(0);
v___x_195_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_194_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_195_;
goto v___jp_114_;
}
else
{
lean_object* v_arg_196_; lean_object* v___x_197_; uint8_t v___x_198_; 
v_arg_196_ = lean_ctor_get(v___x_192_, 1);
lean_inc_ref(v_arg_196_);
v___x_197_ = l_Lean_Expr_appFnCleanup___redArg(v___x_192_);
v___x_198_ = l_Lean_Expr_isApp(v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec_ref(v___x_197_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v___x_199_ = lean_box(0);
v___x_200_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_199_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_200_;
goto v___jp_114_;
}
else
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = l_Lean_Expr_appFnCleanup___redArg(v___x_197_);
v___x_202_ = l_Lean_Expr_isApp(v___x_201_);
if (v___x_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec_ref(v___x_201_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v___x_203_ = lean_box(0);
v___x_204_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_203_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_204_;
goto v___jp_114_;
}
else
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = l_Lean_Expr_appFnCleanup___redArg(v___x_201_);
v___x_206_ = l_Lean_Expr_isApp(v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec_ref(v___x_205_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v___x_207_ = lean_box(0);
v___x_208_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_207_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_208_;
goto v___jp_114_;
}
else
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = l_Lean_Expr_appFnCleanup___redArg(v___x_205_);
v___x_210_ = l_Lean_Expr_isApp(v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec_ref(v___x_209_);
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v___x_211_ = lean_box(0);
v___x_212_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_211_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_212_;
goto v___jp_114_;
}
else
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_209_);
v___x_214_ = l_Lean_Expr_isConstOf(v___x_213_, v___x_183_);
lean_dec_ref(v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v___x_215_ = lean_box(0);
v___x_216_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_215_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
v___y_115_ = v___x_216_;
goto v___jp_114_;
}
else
{
size_t v___x_217_; size_t v___x_218_; uint8_t v___x_219_; 
v___x_217_ = lean_ptr_addr(v_arg_165_);
v___x_218_ = lean_ptr_addr(v_arg_196_);
v___x_219_ = lean_usize_dec_eq(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
size_t v___x_220_; size_t v___x_221_; uint8_t v___x_222_; 
v___x_220_ = lean_ptr_addr(v_arg_160_);
v___x_221_ = lean_ptr_addr(v_arg_191_);
lean_dec_ref(v_arg_191_);
v___x_222_ = lean_usize_dec_eq(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
lean_dec_ref(v_arg_140_);
lean_dec_ref(v_arg_135_);
lean_dec_ref(v_e_91_);
v_contextDependent_103_ = v___x_222_;
goto v___jp_102_;
}
else
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_condition1_226_; lean_object* v_condition2_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11);
v___x_224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14);
lean_inc_ref(v_arg_196_);
lean_inc_ref(v_arg_165_);
v___x_225_ = l_Lean_mkApp4(v___x_224_, v_arg_140_, v_arg_135_, v_arg_165_, v_arg_196_);
v_condition1_226_ = l_Lean_Expr_app___override(v___x_223_, v___x_225_);
v_condition2_227_ = l_Lean_Expr_app___override(v___x_223_, v_e_91_);
v___x_228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17);
v___x_229_ = l_Lean_mkAppB(v___x_228_, v_condition1_226_, v_condition2_227_);
v___x_230_ = l_Lean_Expr_app___override(v___x_223_, v___x_229_);
v___x_231_ = l_Lean_Meta_Sym_shareCommonInc(v___x_230_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24);
v___x_234_ = l_Lean_mkApp4(v___x_233_, v_arg_150_, v_arg_165_, v_arg_196_, v_arg_160_);
v_e_x27_108_ = v_a_232_;
v_proof_109_ = v___x_234_;
v_contextDependent_110_ = v___x_219_;
goto v___jp_107_;
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_arg_196_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
v_a_235_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_231_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_231_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
else
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_condition1_246_; lean_object* v_condition2_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec_ref(v_arg_196_);
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11);
v___x_244_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14);
lean_inc_ref(v_arg_191_);
lean_inc_ref(v_arg_160_);
v___x_245_ = l_Lean_mkApp4(v___x_244_, v_arg_140_, v_arg_135_, v_arg_160_, v_arg_191_);
v_condition1_246_ = l_Lean_Expr_app___override(v___x_243_, v___x_245_);
v_condition2_247_ = l_Lean_Expr_app___override(v___x_243_, v_e_91_);
v___x_248_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17);
v___x_249_ = l_Lean_mkAppB(v___x_248_, v_condition1_246_, v_condition2_247_);
v___x_250_ = l_Lean_Expr_app___override(v___x_243_, v___x_249_);
v___x_251_ = l_Lean_Meta_Sym_shareCommonInc(v___x_250_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v___x_251_, 1);
v___x_253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27);
v___x_254_ = l_Lean_mkApp4(v___x_253_, v_arg_150_, v_arg_165_, v_arg_160_, v_arg_191_);
v___x_255_ = 0;
v_e_x27_108_ = v_a_252_;
v_proof_109_ = v___x_254_;
v_contextDependent_110_ = v___x_255_;
goto v___jp_107_;
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec_ref(v_arg_191_);
lean_dec_ref(v_arg_165_);
lean_dec_ref(v_arg_160_);
lean_dec_ref(v_arg_150_);
v_a_256_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_251_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_251_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
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
}
}
}
v___jp_102_:
{
uint8_t v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = 1;
v___x_105_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_105_, 0, v___x_104_);
lean_ctor_set_uint8(v___x_105_, 1, v_contextDependent_103_);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
v___jp_107_:
{
uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = 1;
v___x_112_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_112_, 0, v_e_x27_108_);
lean_ctor_set(v___x_112_, 1, v_proof_109_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*2, v___x_111_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*2 + 1, v_contextDependent_110_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
v___jp_114_:
{
lean_object* v_a_116_; 
v_a_116_ = lean_ctor_get(v___y_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref(v___y_115_);
if (lean_obj_tag(v_a_116_) == 0)
{
uint8_t v_contextDependent_117_; 
v_contextDependent_117_ = lean_ctor_get_uint8(v_a_116_, 1);
lean_dec_ref_known(v_a_116_, 0);
v_contextDependent_103_ = v_contextDependent_117_;
goto v___jp_102_;
}
else
{
lean_object* v_e_x27_118_; lean_object* v_proof_119_; uint8_t v_contextDependent_120_; 
v_e_x27_118_ = lean_ctor_get(v_a_116_, 0);
lean_inc_ref(v_e_x27_118_);
v_proof_119_ = lean_ctor_get(v_a_116_, 1);
lean_inc_ref(v_proof_119_);
v_contextDependent_120_ = lean_ctor_get_uint8(v_a_116_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_116_, 2);
v_e_x27_108_ = v_e_x27_118_;
v_proof_109_ = v_proof_119_;
v_contextDependent_110_ = v_contextDependent_120_;
goto v___jp_107_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_91_ = stack[0].m_obj;
lean_object* v_a_92_ = stack[1].m_obj;
lean_object* v_a_93_ = stack[2].m_obj;
lean_object* v_a_94_ = stack[3].m_obj;
lean_object* v_a_95_ = stack[4].m_obj;
lean_object* v_a_96_ = stack[5].m_obj;
lean_object* v_a_97_ = stack[6].m_obj;
lean_object* v_a_98_ = stack[7].m_obj;
lean_object* v_a_99_ = stack[8].m_obj;
lean_object* v_a_100_ = stack[9].m_obj;
lean_object* v_res_264_;
v_res_264_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc(v_e_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___boxed(lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc(v_e_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
return v_res_276_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object* v_x_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
v___x_290_ = lean_apply_12(v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, lean_box(0));
return v___x_290_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_277_ = stack[0].m_obj;
lean_object* v___y_278_ = stack[1].m_obj;
lean_object* v___y_279_ = stack[2].m_obj;
lean_object* v___y_280_ = stack[3].m_obj;
lean_object* v___y_281_ = stack[4].m_obj;
lean_object* v___y_282_ = stack[5].m_obj;
lean_object* v___y_283_ = stack[6].m_obj;
lean_object* v___y_284_ = stack[7].m_obj;
lean_object* v___y_285_ = stack[8].m_obj;
lean_object* v___y_286_ = stack[9].m_obj;
lean_object* v___y_287_ = stack[10].m_obj;
lean_object* v___y_288_ = stack[11].m_obj;
lean_object* v_res_291_;
v_res_291_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(v_x_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(lean_object* v_x_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(v_x_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
return v_res_305_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(lean_object* v_mvarId_306_, lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___f_320_; lean_object* v___x_321_; 
lean_inc(v___y_314_);
lean_inc_ref(v___y_313_);
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
lean_inc(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
v___f_320_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_320_, 0, v_x_307_);
lean_closure_set(v___f_320_, 1, v___y_308_);
lean_closure_set(v___f_320_, 2, v___y_309_);
lean_closure_set(v___f_320_, 3, v___y_310_);
lean_closure_set(v___f_320_, 4, v___y_311_);
lean_closure_set(v___f_320_, 5, v___y_312_);
lean_closure_set(v___f_320_, 6, v___y_313_);
lean_closure_set(v___f_320_, 7, v___y_314_);
v___x_321_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_306_, v___f_320_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_321_) == 0)
{
return v___x_321_;
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_321_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_321_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_306_ = stack[0].m_obj;
lean_object* v_x_307_ = stack[1].m_obj;
lean_object* v___y_308_ = stack[2].m_obj;
lean_object* v___y_309_ = stack[3].m_obj;
lean_object* v___y_310_ = stack[4].m_obj;
lean_object* v___y_311_ = stack[5].m_obj;
lean_object* v___y_312_ = stack[6].m_obj;
lean_object* v___y_313_ = stack[7].m_obj;
lean_object* v___y_314_ = stack[8].m_obj;
lean_object* v___y_315_ = stack[9].m_obj;
lean_object* v___y_316_ = stack[10].m_obj;
lean_object* v___y_317_ = stack[11].m_obj;
lean_object* v___y_318_ = stack[12].m_obj;
lean_object* v_res_330_;
v_res_330_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_306_, v_x_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object* v_mvarId_331_, lean_object* v_x_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_331_, v_x_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
return v_res_345_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(lean_object* v_00_u03b1_346_, lean_object* v_mvarId_347_, lean_object* v_x_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_347_, v_x_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_347_ = stack[1].m_obj;
lean_object* v_x_348_ = stack[2].m_obj;
lean_object* v___y_349_ = stack[3].m_obj;
lean_object* v___y_350_ = stack[4].m_obj;
lean_object* v___y_351_ = stack[5].m_obj;
lean_object* v___y_352_ = stack[6].m_obj;
lean_object* v___y_353_ = stack[7].m_obj;
lean_object* v___y_354_ = stack[8].m_obj;
lean_object* v___y_355_ = stack[9].m_obj;
lean_object* v___y_356_ = stack[10].m_obj;
lean_object* v___y_357_ = stack[11].m_obj;
lean_object* v___y_358_ = stack[12].m_obj;
lean_object* v___y_359_ = stack[13].m_obj;
lean_object* v_res_362_;
v_res_362_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(lean_box(0), v_mvarId_347_, v_x_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
stack->m_obj
 = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___boxed(lean_object* v_00_u03b1_363_, lean_object* v_mvarId_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(v_00_u03b1_363_, v_mvarId_364_, v_x_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_378_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(lean_object* v_x_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___closed__0));
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_379_ = stack[0].m_obj;
lean_object* v___y_380_ = stack[1].m_obj;
lean_object* v___y_381_ = stack[2].m_obj;
lean_object* v___y_382_ = stack[3].m_obj;
lean_object* v___y_383_ = stack[4].m_obj;
lean_object* v___y_384_ = stack[5].m_obj;
lean_object* v___y_385_ = stack[6].m_obj;
lean_object* v___y_386_ = stack[7].m_obj;
lean_object* v___y_387_ = stack[8].m_obj;
lean_object* v___y_388_ = stack[9].m_obj;
lean_object* v_res_392_;
v_res_392_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(v_x_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
stack->m_obj
 = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___boxed(lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(v_x_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v_x_393_);
return v_res_404_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(lean_object* v___f_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_config_418_; lean_object* v_maxSteps_419_; lean_object* v___x_420_; lean_object* v_config_421_; lean_object* v___x_422_; lean_object* v_methods_423_; lean_object* v___x_424_; lean_object* v_target_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_config_418_ = lean_ctor_get(v___y_406_, 0);
v_maxSteps_419_ = lean_ctor_get(v_config_418_, 1);
v___x_420_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_419_);
v_config_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_421_, 0, v_maxSteps_419_);
lean_ctor_set(v_config_421_, 1, v___x_420_);
v___x_422_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___boxed), 11, 0);
v_methods_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_423_, 0, v___f_405_);
lean_ctor_set(v_methods_423_, 1, v___x_422_);
v___x_424_ = lean_st_ref_get(v___y_407_);
v_target_425_ = lean_ctor_get(v___x_424_, 2);
lean_inc_ref(v_target_425_);
lean_dec(v___x_424_);
v___x_426_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_425_);
lean_dec_ref(v_target_425_);
v___x_427_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed), 14, 2);
lean_closure_set(v___x_427_, 0, v_methods_423_);
lean_closure_set(v___x_427_, 1, v_config_421_);
v___x_428_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v___x_426_, v___x_427_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
return v___x_428_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_405_ = stack[0].m_obj;
lean_object* v___y_406_ = stack[1].m_obj;
lean_object* v___y_407_ = stack[2].m_obj;
lean_object* v___y_408_ = stack[3].m_obj;
lean_object* v___y_409_ = stack[4].m_obj;
lean_object* v___y_410_ = stack[5].m_obj;
lean_object* v___y_411_ = stack[6].m_obj;
lean_object* v___y_412_ = stack[7].m_obj;
lean_object* v___y_413_ = stack[8].m_obj;
lean_object* v___y_414_ = stack[9].m_obj;
lean_object* v___y_415_ = stack[10].m_obj;
lean_object* v___y_416_ = stack[11].m_obj;
lean_object* v_res_429_;
v_res_429_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(v___f_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed(lean_object* v___f_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(v___f_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_443_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit(builtin);
}
#ifdef __cplusplus
}
#endif

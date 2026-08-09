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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(lean_object* v_x_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___closed__0));
v___x_15_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___boxed(lean_object* v_x_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v_x_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
lean_dec(v___y_25_);
lean_dec_ref(v___y_24_);
lean_dec(v___y_23_);
lean_dec_ref(v___y_22_);
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_19_);
lean_dec_ref(v___y_18_);
lean_dec(v___y_17_);
return v_res_27_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_box(0);
v___x_47_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__10));
v___x_48_ = l_Lean_mkConst(v___x_47_, v___x_46_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = l_Lean_Level_ofNat(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_box(0);
v___x_52_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__12);
v___x_53_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__13);
v___x_55_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2));
v___x_56_ = l_Lean_mkConst(v___x_55_, v___x_54_);
return v___x_56_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_box(0);
v___x_62_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__16));
v___x_63_ = l_Lean_mkConst(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_box(0);
v___x_77_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__23));
v___x_78_ = l_Lean_mkConst(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_box(0);
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__26));
v___x_89_ = l_Lean_mkConst(v___x_88_, v___x_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc(lean_object* v_e_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_e_x27_102_; lean_object* v_proof_103_; uint8_t v_contextDependent_104_; uint8_t v_contextDependent_109_; lean_object* v___y_114_; lean_object* v___x_120_; uint8_t v___x_121_; 
lean_inc_ref(v_e_90_);
v___x_120_ = l_Lean_Expr_cleanupAnnotations(v_e_90_);
v___x_121_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v___x_123_; 
lean_dec_ref(v___x_120_);
lean_dec_ref(v_e_90_);
v___x_122_ = lean_box(0);
v___x_123_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_122_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_123_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v_arg_124_ = lean_ctor_get(v___x_120_, 1);
lean_inc_ref(v_arg_124_);
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
v___x_126_ = l_Lean_Expr_isApp(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec_ref(v___x_125_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_127_ = lean_box(0);
v___x_128_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_127_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_128_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v_arg_129_ = lean_ctor_get(v___x_125_, 1);
lean_inc_ref(v_arg_129_);
v___x_130_ = l_Lean_Expr_appFnCleanup___redArg(v___x_125_);
v___x_131_ = l_Lean_Expr_isApp(v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec_ref(v___x_130_);
lean_dec_ref(v_arg_129_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_132_ = lean_box(0);
v___x_133_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_132_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_133_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_arg_134_ = lean_ctor_get(v___x_130_, 1);
lean_inc_ref(v_arg_134_);
v___x_135_ = l_Lean_Expr_appFnCleanup___redArg(v___x_130_);
v___x_136_ = l_Lean_Expr_isApp(v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; 
lean_dec_ref(v___x_135_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_129_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_137_ = lean_box(0);
v___x_138_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_137_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_138_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_arg_139_ = lean_ctor_get(v___x_135_, 1);
lean_inc_ref(v_arg_139_);
v___x_140_ = l_Lean_Expr_appFnCleanup___redArg(v___x_135_);
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__2));
v___x_142_ = l_Lean_Expr_isConstOf(v___x_140_, v___x_141_);
lean_dec_ref(v___x_140_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_129_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_143_ = lean_box(0);
v___x_144_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_143_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_144_;
goto v___jp_113_;
}
else
{
lean_object* v___x_145_; uint8_t v___x_146_; 
lean_inc_ref(v_arg_139_);
v___x_145_ = l_Lean_Expr_cleanupAnnotations(v_arg_139_);
v___x_146_ = l_Lean_Expr_isApp(v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec_ref(v___x_145_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_129_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_147_ = lean_box(0);
v___x_148_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_147_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_148_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_arg_149_ = lean_ctor_get(v___x_145_, 1);
lean_inc_ref(v_arg_149_);
v___x_150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_145_);
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__4));
v___x_152_ = l_Lean_Expr_isConstOf(v___x_150_, v___x_151_);
lean_dec_ref(v___x_150_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_129_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_153_ = lean_box(0);
v___x_154_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_153_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_154_;
goto v___jp_113_;
}
else
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = l_Lean_Expr_cleanupAnnotations(v_arg_129_);
v___x_156_ = l_Lean_Expr_isApp(v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec_ref(v___x_155_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_157_ = lean_box(0);
v___x_158_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_157_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_158_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_arg_159_ = lean_ctor_get(v___x_155_, 1);
lean_inc_ref(v_arg_159_);
v___x_160_ = l_Lean_Expr_appFnCleanup___redArg(v___x_155_);
v___x_161_ = l_Lean_Expr_isApp(v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec_ref(v___x_160_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_162_ = lean_box(0);
v___x_163_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_162_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_163_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_arg_164_ = lean_ctor_get(v___x_160_, 1);
lean_inc_ref(v_arg_164_);
v___x_165_ = l_Lean_Expr_appFnCleanup___redArg(v___x_160_);
v___x_166_ = l_Lean_Expr_isApp(v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref(v___x_165_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_167_ = lean_box(0);
v___x_168_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_167_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_168_;
goto v___jp_113_;
}
else
{
lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_169_ = l_Lean_Expr_appFnCleanup___redArg(v___x_165_);
v___x_170_ = l_Lean_Expr_isApp(v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; lean_object* v___x_172_; 
lean_dec_ref(v___x_169_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_171_ = lean_box(0);
v___x_172_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_171_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_172_;
goto v___jp_113_;
}
else
{
lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_169_);
v___x_174_ = l_Lean_Expr_isApp(v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec_ref(v___x_173_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_175_ = lean_box(0);
v___x_176_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_175_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_176_;
goto v___jp_113_;
}
else
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = l_Lean_Expr_appFnCleanup___redArg(v___x_173_);
v___x_178_ = l_Lean_Expr_isApp(v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref(v___x_177_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_179_ = lean_box(0);
v___x_180_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_179_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_180_;
goto v___jp_113_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_177_);
v___x_182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__7));
v___x_183_ = l_Lean_Expr_isConstOf(v___x_181_, v___x_182_);
lean_dec_ref(v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; lean_object* v___x_185_; 
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_arg_124_);
lean_dec_ref(v_e_90_);
v___x_184_ = lean_box(0);
v___x_185_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_184_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_185_;
goto v___jp_113_;
}
else
{
lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_186_ = l_Lean_Expr_cleanupAnnotations(v_arg_124_);
v___x_187_ = l_Lean_Expr_isApp(v___x_186_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; lean_object* v___x_189_; 
lean_dec_ref(v___x_186_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v___x_188_ = lean_box(0);
v___x_189_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_188_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_189_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v_arg_190_ = lean_ctor_get(v___x_186_, 1);
lean_inc_ref(v_arg_190_);
v___x_191_ = l_Lean_Expr_appFnCleanup___redArg(v___x_186_);
v___x_192_ = l_Lean_Expr_isApp(v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec_ref(v___x_191_);
lean_dec_ref(v_arg_190_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v___x_193_ = lean_box(0);
v___x_194_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_193_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_194_;
goto v___jp_113_;
}
else
{
lean_object* v_arg_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_arg_195_ = lean_ctor_get(v___x_191_, 1);
lean_inc_ref(v_arg_195_);
v___x_196_ = l_Lean_Expr_appFnCleanup___redArg(v___x_191_);
v___x_197_ = l_Lean_Expr_isApp(v___x_196_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec_ref(v___x_196_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_190_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v___x_198_ = lean_box(0);
v___x_199_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_198_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_199_;
goto v___jp_113_;
}
else
{
lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_200_ = l_Lean_Expr_appFnCleanup___redArg(v___x_196_);
v___x_201_ = l_Lean_Expr_isApp(v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; lean_object* v___x_203_; 
lean_dec_ref(v___x_200_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_190_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v___x_202_ = lean_box(0);
v___x_203_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_202_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_203_;
goto v___jp_113_;
}
else
{
lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = l_Lean_Expr_appFnCleanup___redArg(v___x_200_);
v___x_205_ = l_Lean_Expr_isApp(v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref(v___x_204_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_190_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v___x_206_ = lean_box(0);
v___x_207_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_206_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_207_;
goto v___jp_113_;
}
else
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = l_Lean_Expr_appFnCleanup___redArg(v___x_204_);
v___x_209_ = l_Lean_Expr_isApp(v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec_ref(v___x_208_);
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_190_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v___x_210_ = lean_box(0);
v___x_211_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_210_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_211_;
goto v___jp_113_;
}
else
{
lean_object* v___x_212_; uint8_t v___x_213_; 
v___x_212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_208_);
v___x_213_ = l_Lean_Expr_isConstOf(v___x_212_, v___x_182_);
lean_dec_ref(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_190_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v___x_214_ = lean_box(0);
v___x_215_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0(v___x_214_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
v___y_114_ = v___x_215_;
goto v___jp_113_;
}
else
{
size_t v___x_216_; size_t v___x_217_; uint8_t v___x_218_; 
v___x_216_ = lean_ptr_addr(v_arg_164_);
v___x_217_ = lean_ptr_addr(v_arg_195_);
v___x_218_ = lean_usize_dec_eq(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
size_t v___x_219_; size_t v___x_220_; uint8_t v___x_221_; 
v___x_219_ = lean_ptr_addr(v_arg_159_);
v___x_220_ = lean_ptr_addr(v_arg_190_);
lean_dec_ref(v_arg_190_);
v___x_221_ = lean_usize_dec_eq(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
lean_dec_ref(v_arg_139_);
lean_dec_ref(v_arg_134_);
lean_dec_ref(v_e_90_);
v_contextDependent_109_ = v___x_221_;
goto v___jp_108_;
}
else
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_condition1_225_; lean_object* v_condition2_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_222_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11);
v___x_223_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14);
lean_inc_ref(v_arg_195_);
lean_inc_ref(v_arg_164_);
v___x_224_ = l_Lean_mkApp4(v___x_223_, v_arg_139_, v_arg_134_, v_arg_164_, v_arg_195_);
v_condition1_225_ = l_Lean_Expr_app___override(v___x_222_, v___x_224_);
v_condition2_226_ = l_Lean_Expr_app___override(v___x_222_, v_e_90_);
v___x_227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17);
v___x_228_ = l_Lean_mkAppB(v___x_227_, v_condition1_225_, v_condition2_226_);
v___x_229_ = l_Lean_Expr_app___override(v___x_222_, v___x_228_);
v___x_230_ = l_Lean_Meta_Sym_shareCommonInc(v___x_229_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__24);
v___x_233_ = l_Lean_mkApp4(v___x_232_, v_arg_149_, v_arg_164_, v_arg_195_, v_arg_159_);
v_e_x27_102_ = v_a_231_;
v_proof_103_ = v___x_233_;
v_contextDependent_104_ = v___x_218_;
goto v___jp_101_;
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_arg_195_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
v_a_234_ = lean_ctor_get(v___x_230_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_230_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_230_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v_condition1_245_; lean_object* v_condition2_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_dec_ref(v_arg_195_);
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__11);
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__14);
lean_inc_ref(v_arg_190_);
lean_inc_ref(v_arg_159_);
v___x_244_ = l_Lean_mkApp4(v___x_243_, v_arg_139_, v_arg_134_, v_arg_159_, v_arg_190_);
v_condition1_245_ = l_Lean_Expr_app___override(v___x_242_, v___x_244_);
v_condition2_246_ = l_Lean_Expr_app___override(v___x_242_, v_e_90_);
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__17);
v___x_248_ = l_Lean_mkAppB(v___x_247_, v_condition1_245_, v_condition2_246_);
v___x_249_ = l_Lean_Expr_app___override(v___x_242_, v___x_248_);
v___x_250_ = l_Lean_Meta_Sym_shareCommonInc(v___x_249_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_a_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v___x_250_, 1);
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27, &l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___closed__27);
v___x_253_ = l_Lean_mkApp4(v___x_252_, v_arg_149_, v_arg_164_, v_arg_159_, v_arg_190_);
v___x_254_ = 0;
v_e_x27_102_ = v_a_251_;
v_proof_103_ = v___x_253_;
v_contextDependent_104_ = v___x_254_;
goto v___jp_101_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_arg_190_);
lean_dec_ref(v_arg_164_);
lean_dec_ref(v_arg_159_);
lean_dec_ref(v_arg_149_);
v_a_255_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_250_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_250_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
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
v___jp_101_:
{
uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = 1;
v___x_106_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_106_, 0, v_e_x27_102_);
lean_ctor_set(v___x_106_, 1, v_proof_103_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*2, v___x_105_);
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*2 + 1, v_contextDependent_104_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
v___jp_108_:
{
uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = 1;
v___x_111_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_111_, 0, v___x_110_);
lean_ctor_set_uint8(v___x_111_, 1, v_contextDependent_109_);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v_a_115_; 
v_a_115_ = lean_ctor_get(v___y_114_, 0);
lean_inc(v_a_115_);
lean_dec_ref(v___y_114_);
if (lean_obj_tag(v_a_115_) == 0)
{
uint8_t v_contextDependent_116_; 
v_contextDependent_116_ = lean_ctor_get_uint8(v_a_115_, 1);
lean_dec_ref_known(v_a_115_, 0);
v_contextDependent_109_ = v_contextDependent_116_;
goto v___jp_108_;
}
else
{
lean_object* v_e_x27_117_; lean_object* v_proof_118_; uint8_t v_contextDependent_119_; 
v_e_x27_117_ = lean_ctor_get(v_a_115_, 0);
lean_inc_ref(v_e_x27_117_);
v_proof_118_ = lean_ctor_get(v_a_115_, 1);
lean_inc_ref(v_proof_118_);
v_contextDependent_119_ = lean_ctor_get_uint8(v_a_115_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_115_, 2);
v_e_x27_102_ = v_e_x27_117_;
v_proof_103_ = v_proof_118_;
v_contextDependent_104_ = v_contextDependent_119_;
goto v___jp_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___boxed(lean_object* v_e_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc(v_e_263_, v_a_264_, v_a_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; 
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
v___x_288_ = lean_apply_12(v_x_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed(lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0(v_x_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(lean_object* v_mvarId_303_, lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___f_317_; lean_object* v___x_318_; 
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_317_, 0, v_x_304_);
lean_closure_set(v___f_317_, 1, v___y_305_);
lean_closure_set(v___f_317_, 2, v___y_306_);
lean_closure_set(v___f_317_, 3, v___y_307_);
lean_closure_set(v___f_317_, 4, v___y_308_);
lean_closure_set(v___f_317_, 5, v___y_309_);
lean_closure_set(v___f_317_, 6, v___y_310_);
lean_closure_set(v___f_317_, 7, v___y_311_);
v___x_318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_303_, v___f_317_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_318_) == 0)
{
return v___x_318_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object* v_mvarId_327_, lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_327_, v_x_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(lean_object* v_00_u03b1_342_, lean_object* v_mvarId_343_, lean_object* v_x_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v_mvarId_343_, v_x_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___boxed(lean_object* v_00_u03b1_358_, lean_object* v_mvarId_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0(v_00_u03b1_358_, v_mvarId_359_, v_x_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___lam__0___closed__0));
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0___boxed(lean_object* v_x_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__0(v_x_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v_x_387_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(lean_object* v___f_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_config_412_; lean_object* v___x_413_; lean_object* v_maxSteps_414_; lean_object* v_target_415_; lean_object* v___x_416_; lean_object* v_config_417_; lean_object* v___x_418_; lean_object* v_methods_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_config_412_ = lean_ctor_get(v___y_400_, 0);
v___x_413_ = lean_st_ref_get(v___y_401_);
v_maxSteps_414_ = lean_ctor_get(v_config_412_, 1);
v_target_415_ = lean_ctor_get(v___x_413_, 4);
lean_inc_ref(v_target_415_);
lean_dec(v___x_413_);
v___x_416_ = lean_unsigned_to_nat(2u);
lean_inc(v_maxSteps_414_);
v_config_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_417_, 0, v_maxSteps_414_);
lean_ctor_set(v_config_417_, 1, v___x_416_);
v___x_418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_BVDecide_Normalize_ShortCircuit_0__Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitProc___boxed), 11, 0);
v_methods_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_419_, 0, v___f_399_);
lean_ctor_set(v_methods_419_, 1, v___x_418_);
v___x_420_ = l_Lean_Meta_Tactic_BVDecide_Normalize_Target_mvarId(v_target_415_);
lean_dec_ref(v_target_415_);
v___x_421_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapSimpHyps___boxed), 14, 2);
lean_closure_set(v___x_421_, 0, v_methods_419_);
lean_closure_set(v___x_421_, 1, v_config_417_);
v___x_422_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass_spec__0___redArg(v___x_420_, v___x_421_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1___boxed(lean_object* v___f_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Tactic_BVDecide_Normalize_shortCircuitPass___lam__1(v___f_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
return v_res_436_;
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

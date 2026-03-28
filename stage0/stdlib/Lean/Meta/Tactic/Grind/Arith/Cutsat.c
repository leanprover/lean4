// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr public import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Inv public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var public import Lean.Meta.Tactic.Grind.Arith.Cutsat.EqCnstr public import Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Model public import Lean.Meta.Tactic.Grind.Arith.Cutsat.MBTC public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat public import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing public import Lean.Meta.Tactic.Grind.Arith.Cutsat.VarRename public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Action
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_lia___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Arith"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 133, 41, 173, 115, 110, 60, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Cutsat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(71, 21, 220, 222, 34, 20, 213, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(58, 72, 177, 57, 76, 236, 112, 50)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(91, 74, 164, 236, 124, 201, 46, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(179, 245, 229, 61, 54, 31, 201, 170)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 69, 156, 196, 164, 74, 158, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 163, 94, 129, 36, 25, 70, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 124, 71, 125, 239, 252, 212, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 46, 119, 58, 38, 44, 101, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 197, 124, 244, 209, 46, 178, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 148, 151, 80, 98, 103, 30, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 192, 33, 42, 174, 230, 128, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 90, 145, 77, 215, 94, 47, 46)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 254, 117, 134, 11, 144, 211, 3)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(225, 121, 97, 189, 19, 243, 110, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 215, 180, 167, 81, 110, 45, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1544613409) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(84, 68, 72, 248, 252, 193, 191, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 132, 191, 154, 49, 146, 18, 89)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 253, 204, 211, 164, 156, 155, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(142, 227, 73, 233, 112, 124, 78, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "nonlinear"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 58, 156, 167, 134, 22, 231, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(172, 153, 248, 110, 186, 235, 101, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1905195225) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(121, 105, 12, 160, 85, 181, 203, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 21, 214, 26, 213, 192, 106, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(150, 128, 24, 154, 247, 75, 27, 236)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(215, 191, 153, 147, 216, 187, 242, 245)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(537780665) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(120, 231, 214, 101, 225, 91, 226, 132)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 169, 167, 25, 184, 10, 44, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 132, 63, 204, 45, 127, 140, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(114, 198, 79, 130, 251, 247, 117, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(177, 38, 232, 206, 222, 75, 121, 224)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 204, 174, 99, 3, 215, 140, 75)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 213, 16, 64, 1, 14, 244, 141)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 45, 160, 130, 43, 179, 195, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1839615665) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(182, 85, 43, 78, 198, 235, 74, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 51, 81, 189, 14, 103, 233, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 89, 162, 230, 201, 144, 245, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(212, 221, 72, 20, 13, 52, 34, 124)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 149, 0, 200, 120, 117, 225, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(179901175) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(218, 203, 232, 198, 198, 192, 139, 129)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 138, 106, 4, 11, 74, 136, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 131, 63, 111, 108, 231, 157, 161)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(248, 196, 163, 218, 108, 240, 172, 34)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(798741302) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(195, 165, 158, 99, 134, 204, 12, 229)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 164, 248, 147, 3, 20, 248, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 70, 91, 218, 133, 26, 43, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(37, 70, 196, 157, 55, 2, 171, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 58, 158, 115, 200, 214, 28, 68)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2124775375) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(119, 52, 6, 138, 84, 174, 114, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 132, 150, 173, 12, 87, 4, 23)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 152, 206, 124, 193, 78, 118, 156)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 218, 58, 104, 44, 117, 122, 242)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assign"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 193, 134, 128, 236, 17, 208, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1019473888) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(112, 199, 44, 52, 1, 32, 116, 127)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(39, 150, 103, 116, 98, 197, 150, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 80, 134, 15, 19, 171, 78, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(234, 50, 221, 21, 121, 237, 167, 185)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "conflict"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 33, 244, 131, 103, 39, 179, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(655095259) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(91, 96, 99, 206, 123, 52, 154, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 136, 173, 236, 170, 227, 119, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 175, 213, 205, 66, 72, 208, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(29, 9, 49, 150, 183, 35, 142, 17)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "backtrack"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(66, 156, 104, 79, 45, 158, 161, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(34, 238, 188, 187, 128, 53, 130, 20)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 155, 160, 222, 187, 19, 79, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cnstrs"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 244, 212, 181, 93, 65, 224, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reorder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 159, 191, 181, 87, 7, 198, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(372033) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 156, 117, 240, 210, 69, 154, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 7, 142, 234, 57, 99, 10, 155)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 144, 203, 119, 222, 240, 140, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(214, 49, 244, 132, 233, 67, 45, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "elimEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 203, 12, 30, 164, 97, 50, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(69582620) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 69, 74, 156, 166, 161, 38, 123)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 134, 166, 107, 52, 11, 113, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 159, 107, 107, 201, 24, 95, 183)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(117, 172, 199, 224, 94, 146, 233, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_processNewDiseq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_mbtc___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_lia___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_check___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Cutsat_checkInvariants___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_94_ = 0;
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_96_ = l_Lean_registerTraceClass(v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2____boxed(lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_();
return v_res_98_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_unsigned_to_nat(2341206022u);
v___x_105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_106_ = l_Lean_Name_num___override(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_109_ = l_Lean_Name_str___override(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_112_ = l_Lean_Name_str___override(v___x_111_, v___x_110_);
return v___x_112_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_113_ = lean_unsigned_to_nat(2u);
v___x_114_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_115_ = l_Lean_Name_num___override(v___x_114_, v___x_113_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_));
v___x_118_ = 0;
v___x_119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_120_ = l_Lean_registerTraceClass(v___x_117_, v___x_118_, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2____boxed(lean_object* v_a_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_();
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_));
v___x_142_ = 0;
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_));
v___x_144_ = l_Lean_registerTraceClass(v___x_141_, v___x_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2____boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_));
v___x_166_ = 0;
v___x_167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_));
v___x_168_ = l_Lean_registerTraceClass(v___x_165_, v___x_166_, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2____boxed(lean_object* v_a_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_();
return v_res_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_177_ = lean_unsigned_to_nat(3140426734u);
v___x_178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_179_ = l_Lean_Name_num___override(v___x_178_, v___x_177_);
return v___x_179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_182_ = l_Lean_Name_str___override(v___x_181_, v___x_180_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_185_ = l_Lean_Name_str___override(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_unsigned_to_nat(2u);
v___x_187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_188_ = l_Lean_Name_num___override(v___x_187_, v___x_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_));
v___x_191_ = 0;
v___x_192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_193_ = l_Lean_registerTraceClass(v___x_190_, v___x_191_, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2____boxed(lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_();
return v_res_195_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = lean_unsigned_to_nat(2860508919u);
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_204_ = l_Lean_Name_num___override(v___x_203_, v___x_202_);
return v___x_204_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_207_ = l_Lean_Name_str___override(v___x_206_, v___x_205_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_210_ = l_Lean_Name_str___override(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_211_ = lean_unsigned_to_nat(2u);
v___x_212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_213_ = l_Lean_Name_num___override(v___x_212_, v___x_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_));
v___x_216_ = 0;
v___x_217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_218_ = l_Lean_registerTraceClass(v___x_215_, v___x_216_, v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2____boxed(lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_();
return v_res_220_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_unsigned_to_nat(2288204289u);
v___x_228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_229_ = l_Lean_Name_num___override(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_231_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_232_ = l_Lean_Name_str___override(v___x_231_, v___x_230_);
return v___x_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_235_ = l_Lean_Name_str___override(v___x_234_, v___x_233_);
return v___x_235_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_unsigned_to_nat(2u);
v___x_237_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_238_ = l_Lean_Name_num___override(v___x_237_, v___x_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_));
v___x_241_ = 0;
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_243_ = l_Lean_registerTraceClass(v___x_240_, v___x_241_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2____boxed(lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_();
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_));
v___x_265_ = 0;
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_));
v___x_267_ = l_Lean_registerTraceClass(v___x_264_, v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2____boxed(lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_290_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_));
v___x_291_ = 0;
v___x_292_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_));
v___x_293_ = l_Lean_registerTraceClass(v___x_290_, v___x_291_, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2____boxed(lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_();
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_));
v___x_316_ = 0;
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_));
v___x_318_ = l_Lean_registerTraceClass(v___x_315_, v___x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2____boxed(lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_();
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_341_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_));
v___x_342_ = 1;
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_));
v___x_344_ = l_Lean_registerTraceClass(v___x_341_, v___x_342_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2____boxed(lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_();
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_));
v___x_368_ = 1;
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_));
v___x_370_ = l_Lean_registerTraceClass(v___x_367_, v___x_368_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2____boxed(lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_();
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_393_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_));
v___x_394_ = 1;
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_));
v___x_396_ = l_Lean_registerTraceClass(v___x_393_, v___x_394_, v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2____boxed(lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_();
return v_res_398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_unsigned_to_nat(2719854357u);
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_408_ = l_Lean_Name_num___override(v___x_407_, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_410_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_411_ = l_Lean_Name_str___override(v___x_410_, v___x_409_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_413_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_414_ = l_Lean_Name_str___override(v___x_413_, v___x_412_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_415_ = lean_unsigned_to_nat(2u);
v___x_416_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_417_ = l_Lean_Name_num___override(v___x_416_, v___x_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_));
v___x_420_ = 1;
v___x_421_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_422_ = l_Lean_registerTraceClass(v___x_419_, v___x_420_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2____boxed(lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_();
return v_res_424_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_unsigned_to_nat(2389350560u);
v___x_432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_433_ = l_Lean_Name_num___override(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_436_ = l_Lean_Name_str___override(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_439_ = l_Lean_Name_str___override(v___x_438_, v___x_437_);
return v___x_439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_unsigned_to_nat(2u);
v___x_441_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_442_ = l_Lean_Name_num___override(v___x_441_, v___x_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_));
v___x_445_ = 0;
v___x_446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_447_ = l_Lean_registerTraceClass(v___x_444_, v___x_445_, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2____boxed(lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_();
return v_res_449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_unsigned_to_nat(2594082301u);
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_458_ = l_Lean_Name_num___override(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_460_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_461_ = l_Lean_Name_str___override(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_463_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_464_ = l_Lean_Name_str___override(v___x_463_, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(2u);
v___x_466_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_467_ = l_Lean_Name_num___override(v___x_466_, v___x_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_));
v___x_470_ = 0;
v___x_471_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_472_ = l_Lean_registerTraceClass(v___x_469_, v___x_470_, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2____boxed(lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_();
return v_res_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = lean_unsigned_to_nat(3902918421u);
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_484_ = l_Lean_Name_num___override(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_486_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_487_ = l_Lean_Name_str___override(v___x_486_, v___x_485_);
return v___x_487_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_488_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_490_ = l_Lean_Name_str___override(v___x_489_, v___x_488_);
return v___x_490_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(2u);
v___x_492_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_493_ = l_Lean_Name_num___override(v___x_492_, v___x_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_));
v___x_496_ = 0;
v___x_497_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_498_ = l_Lean_registerTraceClass(v___x_495_, v___x_496_, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2____boxed(lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_();
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_));
v___x_522_ = 0;
v___x_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_));
v___x_524_ = l_Lean_registerTraceClass(v___x_521_, v___x_522_, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2____boxed(lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_();
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_546_; uint8_t v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_));
v___x_547_ = 0;
v___x_548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_));
v___x_549_ = l_Lean_registerTraceClass(v___x_546_, v___x_547_, v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2____boxed(lean_object* v_a_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_();
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_560_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_563_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_565_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_566_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_568_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_560_, v___x_561_, v___x_562_, v___x_563_, v___x_564_, v___x_565_, v___x_566_, v___x_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2____boxed(lean_object* v_a_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_();
return v_res_570_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_EqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(builtin);
}
#ifdef __cplusplus
}
#endif

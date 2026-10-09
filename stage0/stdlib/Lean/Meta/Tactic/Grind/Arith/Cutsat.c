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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reorder"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(144, 165, 104, 86, 70, 21, 218, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 65, 210, 255, 142, 133, 148, 120)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 159, 191, 181, 87, 7, 198, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),((lean_object*)(((size_t)(372033) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(60, 156, 117, 240, 210, 69, 154, 152)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(147, 7, 142, 234, 57, 99, 10, 155)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 144, 203, 119, 222, 240, 140, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(214, 49, 244, 132, 233, 67, 45, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__value;
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_97_;
v_res_97_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_();
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2____boxed(lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_();
return v_res_99_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(2341206022u);
v___x_106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_107_ = l_Lean_Name_num___override(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_109_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_110_ = l_Lean_Name_str___override(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_113_ = l_Lean_Name_str___override(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_116_ = l_Lean_Name_num___override(v___x_115_, v___x_114_);
return v___x_116_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_));
v___x_119_ = 0;
v___x_120_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_);
v___x_121_ = l_Lean_registerTraceClass(v___x_118_, v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_122_;
v_res_122_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_();
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2____boxed(lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2341206022____hygCtx___hyg_2_();
return v_res_124_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_));
v___x_144_ = 0;
v___x_145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_));
v___x_146_ = l_Lean_registerTraceClass(v___x_143_, v___x_144_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_147_;
v_res_147_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_();
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2____boxed(lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1905195225____hygCtx___hyg_2_();
return v_res_149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(3762227469u);
v___x_156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_157_ = l_Lean_Name_num___override(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_);
v___x_160_ = l_Lean_Name_str___override(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_162_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_);
v___x_163_ = l_Lean_Name_str___override(v___x_162_, v___x_161_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_unsigned_to_nat(2u);
v___x_165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_);
v___x_166_ = l_Lean_Name_num___override(v___x_165_, v___x_164_);
return v___x_166_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_));
v___x_169_ = 0;
v___x_170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_);
v___x_171_ = l_Lean_registerTraceClass(v___x_168_, v___x_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_172_;
v_res_172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_();
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2____boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_();
return v_res_174_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_193_; uint8_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_));
v___x_194_ = 0;
v___x_195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_));
v___x_196_ = l_Lean_registerTraceClass(v___x_193_, v___x_194_, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_197_;
v_res_197_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_();
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2____boxed(lean_object* v_a_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_537780665____hygCtx___hyg_2_();
return v_res_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(3140426734u);
v___x_207_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_208_ = l_Lean_Name_num___override(v___x_207_, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_210_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_211_ = l_Lean_Name_str___override(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_214_ = l_Lean_Name_str___override(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = lean_unsigned_to_nat(2u);
v___x_216_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_217_ = l_Lean_Name_num___override(v___x_216_, v___x_215_);
return v___x_217_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_219_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_));
v___x_220_ = 0;
v___x_221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_);
v___x_222_ = l_Lean_registerTraceClass(v___x_219_, v___x_220_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_223_;
v_res_223_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_();
stack->m_obj
 = v_res_223_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2____boxed(lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3140426734____hygCtx___hyg_2_();
return v_res_225_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(2860508919u);
v___x_233_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_234_ = l_Lean_Name_num___override(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_236_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_237_ = l_Lean_Name_str___override(v___x_236_, v___x_235_);
return v___x_237_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_238_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_240_ = l_Lean_Name_str___override(v___x_239_, v___x_238_);
return v___x_240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_241_ = lean_unsigned_to_nat(2u);
v___x_242_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_243_ = l_Lean_Name_num___override(v___x_242_, v___x_241_);
return v___x_243_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_));
v___x_246_ = 0;
v___x_247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_);
v___x_248_ = l_Lean_registerTraceClass(v___x_245_, v___x_246_, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_249_;
v_res_249_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_();
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2____boxed(lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2860508919____hygCtx___hyg_2_();
return v_res_251_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_unsigned_to_nat(2288204289u);
v___x_259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_260_ = l_Lean_Name_num___override(v___x_259_, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_262_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_263_ = l_Lean_Name_str___override(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_266_ = l_Lean_Name_str___override(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_unsigned_to_nat(2u);
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_269_ = l_Lean_Name_num___override(v___x_268_, v___x_267_);
return v___x_269_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_271_; uint8_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_));
v___x_272_ = 0;
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_);
v___x_274_ = l_Lean_registerTraceClass(v___x_271_, v___x_272_, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_275_;
v_res_275_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_();
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2____boxed(lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2288204289____hygCtx___hyg_2_();
return v_res_277_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_));
v___x_297_ = 0;
v___x_298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_));
v___x_299_ = l_Lean_registerTraceClass(v___x_296_, v___x_297_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_300_;
v_res_300_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_();
stack->m_obj
 = v_res_300_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2____boxed(lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1839615665____hygCtx___hyg_2_();
return v_res_302_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_323_; uint8_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_));
v___x_324_ = 0;
v___x_325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_));
v___x_326_ = l_Lean_registerTraceClass(v___x_323_, v___x_324_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_327_;
v_res_327_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_();
stack->m_obj
 = v_res_327_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2____boxed(lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_179901175____hygCtx___hyg_2_();
return v_res_329_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_));
v___x_350_ = 0;
v___x_351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_));
v___x_352_ = l_Lean_registerTraceClass(v___x_349_, v___x_350_, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_353_;
v_res_353_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_();
stack->m_obj
 = v_res_353_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2____boxed(lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_798741302____hygCtx___hyg_2_();
return v_res_355_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_));
v___x_377_ = 1;
v___x_378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_));
v___x_379_ = l_Lean_registerTraceClass(v___x_376_, v___x_377_, v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_380_;
v_res_380_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_();
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2____boxed(lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2124775375____hygCtx___hyg_2_();
return v_res_382_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_403_; uint8_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_));
v___x_404_ = 1;
v___x_405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_));
v___x_406_ = l_Lean_registerTraceClass(v___x_403_, v___x_404_, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_407_;
v_res_407_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_();
stack->m_obj
 = v_res_407_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2____boxed(lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1019473888____hygCtx___hyg_2_();
return v_res_409_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_430_; uint8_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_));
v___x_431_ = 1;
v___x_432_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_));
v___x_433_ = l_Lean_registerTraceClass(v___x_430_, v___x_431_, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_434_;
v_res_434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_();
stack->m_obj
 = v_res_434_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2____boxed(lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_655095259____hygCtx___hyg_2_();
return v_res_436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_unsigned_to_nat(2719854357u);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_446_ = l_Lean_Name_num___override(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_449_ = l_Lean_Name_str___override(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_452_ = l_Lean_Name_str___override(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(2u);
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_455_ = l_Lean_Name_num___override(v___x_454_, v___x_453_);
return v___x_455_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_));
v___x_458_ = 1;
v___x_459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_);
v___x_460_ = l_Lean_registerTraceClass(v___x_457_, v___x_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_();
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2____boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2719854357____hygCtx___hyg_2_();
return v_res_463_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(2389350560u);
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_472_ = l_Lean_Name_num___override(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_475_ = l_Lean_Name_str___override(v___x_474_, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_477_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_478_ = l_Lean_Name_str___override(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_unsigned_to_nat(2u);
v___x_480_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_481_ = l_Lean_Name_num___override(v___x_480_, v___x_479_);
return v___x_481_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_483_; uint8_t v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_));
v___x_484_ = 0;
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_);
v___x_486_ = l_Lean_registerTraceClass(v___x_483_, v___x_484_, v___x_485_);
return v___x_486_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_487_;
v_res_487_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_();
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2____boxed(lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2389350560____hygCtx___hyg_2_();
return v_res_489_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_unsigned_to_nat(2594082301u);
v___x_497_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_498_ = l_Lean_Name_num___override(v___x_497_, v___x_496_);
return v___x_498_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_500_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_501_ = l_Lean_Name_str___override(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_503_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_504_ = l_Lean_Name_str___override(v___x_503_, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_unsigned_to_nat(2u);
v___x_506_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_507_ = l_Lean_Name_num___override(v___x_506_, v___x_505_);
return v___x_507_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_509_; uint8_t v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_509_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_));
v___x_510_ = 0;
v___x_511_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_);
v___x_512_ = l_Lean_registerTraceClass(v___x_509_, v___x_510_, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_513_;
v_res_513_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_();
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2____boxed(lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_2594082301____hygCtx___hyg_2_();
return v_res_515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = lean_unsigned_to_nat(3902918421u);
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_525_ = l_Lean_Name_num___override(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_528_ = l_Lean_Name_str___override(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_1544613409____hygCtx___hyg_2_));
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_531_ = l_Lean_Name_str___override(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_unsigned_to_nat(2u);
v___x_533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_534_ = l_Lean_Name_num___override(v___x_533_, v___x_532_);
return v___x_534_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_536_; uint8_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_));
v___x_537_ = 0;
v___x_538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_);
v___x_539_ = l_Lean_registerTraceClass(v___x_536_, v___x_537_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_540_;
v_res_540_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_();
stack->m_obj
 = v_res_540_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2____boxed(lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3902918421____hygCtx___hyg_2_();
return v_res_542_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_562_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_));
v___x_563_ = 0;
v___x_564_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_));
v___x_565_ = l_Lean_registerTraceClass(v___x_562_, v___x_563_, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_566_;
v_res_566_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_();
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2____boxed(lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_372033____hygCtx___hyg_2_();
return v_res_568_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_));
v___x_589_ = 0;
v___x_590_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_));
v___x_591_ = l_Lean_registerTraceClass(v___x_588_, v___x_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_592_;
v_res_592_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_();
stack->m_obj
 = v_res_592_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2____boxed(lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_69582620____hygCtx___hyg_2_();
return v_res_594_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_603_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_610_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_));
v___x_611_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_603_, v___x_604_, v___x_605_, v___x_606_, v___x_607_, v___x_608_, v___x_609_, v___x_610_);
return v___x_611_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_612_;
v_res_612_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_();
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2____boxed(lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_340198817____hygCtx___hyg_2_();
return v_res_614_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_3762227469____hygCtx___hyg_2_();
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

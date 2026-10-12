// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.Types public import Lean.Meta.Tactic.Grind.Arith.Linear.Util public import Lean.Meta.Tactic.Grind.Arith.Linear.Var public import Lean.Meta.Tactic.Grind.Arith.Linear.StructId public import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr public import Lean.Meta.Tactic.Grind.Arith.Linear.Reify public import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr public import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr public import Lean.Meta.Tactic.Grind.Arith.Linear.Proof public import Lean.Meta.Tactic.Grind.Arith.Linear.SearchM public import Lean.Meta.Tactic.Grind.Arith.Linear.Search public import Lean.Meta.Tactic.Grind.Arith.Linear.PropagateEq public import Lean.Meta.Tactic.Grind.Arith.Linear.Internalize public import Lean.Meta.Tactic.Grind.Arith.Linear.Model public import Lean.Meta.Tactic.Grind.Arith.Linear.PP public import Lean.Meta.Tactic.Grind.Arith.Linear.Inv public import Lean.Meta.Tactic.Grind.Arith.Linear.MBTC public import Lean.Meta.Tactic.Grind.Arith.Linear.VarRename public import Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule public import Lean.Meta.Tactic.Grind.Arith.Linear.Action
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l_Lean_Meta_Grind_Arith_Linear_internalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Action_linarith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linarith"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Arith"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 133, 41, 173, 115, 110, 60, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 82, 161, 199, 59, 37, 44, 179)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(229, 89, 192, 107, 208, 206, 74, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 72, 237, 133, 217, 209, 245, 200)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 172, 87, 165, 243, 208, 130, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 116, 83, 76, 10, 50, 121, 107)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 25, 186, 103, 170, 4, 41, 154)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(191, 11, 196, 194, 21, 37, 84, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 56, 58, 116, 255, 248, 38, 190)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 177, 21, 150, 208, 245, 46, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 60, 202, 68, 94, 163, 75, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 67, 110, 154, 47, 26, 213, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__28_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 44, 25, 69, 39, 81, 159, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__29_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 100, 45, 11, 96, 243, 191, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__30_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 94, 69, 196, 29, 237, 254, 31)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__31_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(108, 45, 63, 230, 184, 42, 233, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1977064142) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(122, 117, 58, 112, 246, 196, 240, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__33_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 208, 113, 149, 154, 229, 196, 229)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__35_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(149, 14, 202, 37, 75, 161, 56, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__37_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(24, 169, 133, 128, 87, 86, 228, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 76, 129, 208, 175, 107, 80, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(864946378) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(210, 194, 150, 168, 24, 183, 255, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 234, 10, 193, 255, 33, 147, 52)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(125, 226, 3, 36, 40, 82, 8, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(144, 232, 203, 93, 85, 182, 97, 135)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "model"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 255, 209, 221, 117, 20, 143, 66)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(273425714) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(205, 247, 61, 135, 205, 15, 31, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 183, 0, 151, 161, 248, 21, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(130, 137, 248, 68, 234, 3, 202, 134)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(219, 9, 153, 243, 231, 230, 119, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 30, 10, 54, 124, 46, 5, 170)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(118464817) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(201, 213, 176, 203, 181, 57, 14, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 219, 165, 179, 146, 223, 47, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(38, 40, 237, 239, 182, 44, 177, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(103, 177, 71, 106, 61, 192, 45, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 147, 43, 157, 153, 42, 8, 6)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(108, 151, 24, 43, 11, 190, 144, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1769673126) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(16, 224, 74, 27, 90, 82, 225, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(135, 172, 101, 212, 17, 97, 170, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(207, 182, 38, 213, 161, 200, 98, 98)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(138, 131, 166, 201, 60, 97, 191, 11)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ignored"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 135, 131, 0, 162, 156, 15, 149)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 36, 82, 219, 127, 154, 201, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(193, 67, 1, 106, 4, 67, 211, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "search"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1878016030) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(234, 217, 242, 85, 118, 214, 216, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(37, 107, 218, 81, 44, 206, 140, 69)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 76, 193, 163, 211, 6, 89, 72)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(8, 139, 96, 41, 175, 62, 69, 50)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "conflict"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 96, 199, 219, 74, 81, 53, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(356702522) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(212, 195, 103, 92, 150, 187, 185, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 248, 196, 24, 165, 13, 145, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 76, 236, 76, 82, 105, 42, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 84, 154, 154, 13, 138, 220, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assign"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 219, 209, 154, 141, 10, 194, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1398474614) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(206, 218, 236, 18, 216, 220, 186, 9)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 133, 44, 59, 141, 117, 65, 19)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 149, 218, 220, 27, 134, 154, 144)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(172, 71, 37, 240, 158, 231, 92, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 40, 205, 216, 38, 159, 186, 145)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1427258088) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(245, 126, 217, 26, 215, 106, 5, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(102, 123, 103, 120, 223, 35, 125, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 33, 89, 229, 241, 105, 30, 42)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(3, 196, 116, 27, 63, 38, 84, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "backtrack"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 173, 66, 15, 213, 143, 53, 172)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 181, 179, 222, 180, 216, 89, 61)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 101, 68, 215, 12, 32, 3, 85)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 1, 87, 68, 102, 24, 231, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_internalize___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_processNewEq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_processNewDiseq___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_mbtc___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Action_linarith___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_check___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_94_ = 0;
v___x_95_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__38_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_96_ = l_Lean_registerTraceClass(v___x_93_, v___x_94_, v___x_95_);
return v___x_96_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_97_;
v_res_97_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_();
stack->m_obj
 = v_res_97_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2____boxed(lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_();
return v_res_99_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_));
v___x_119_ = 0;
v___x_120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_));
v___x_121_ = l_Lean_registerTraceClass(v___x_118_, v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_122_;
v_res_122_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_();
stack->m_obj
 = v_res_122_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2____boxed(lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_();
return v_res_124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = lean_unsigned_to_nat(2867706376u);
v___x_131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_132_ = l_Lean_Name_num___override(v___x_131_, v___x_130_);
return v___x_132_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_134_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
v___x_135_ = l_Lean_Name_str___override(v___x_134_, v___x_133_);
return v___x_135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_137_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
v___x_138_ = l_Lean_Name_str___override(v___x_137_, v___x_136_);
return v___x_138_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_unsigned_to_nat(2u);
v___x_140_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
v___x_141_ = l_Lean_Name_num___override(v___x_140_, v___x_139_);
return v___x_141_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_));
v___x_144_ = 0;
v___x_145_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_);
v___x_146_ = l_Lean_registerTraceClass(v___x_143_, v___x_144_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_147_;
v_res_147_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_();
stack->m_obj
 = v_res_147_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2____boxed(lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_();
return v_res_149_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_168_; uint8_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_));
v___x_169_ = 0;
v___x_170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_));
v___x_171_ = l_Lean_registerTraceClass(v___x_168_, v___x_169_, v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_172_;
v_res_172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_();
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2____boxed(lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_();
return v_res_174_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_));
v___x_195_ = 1;
v___x_196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_));
v___x_197_ = l_Lean_registerTraceClass(v___x_194_, v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_198_;
v_res_198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_();
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2____boxed(lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_();
return v_res_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_unsigned_to_nat(3761402091u);
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_209_ = l_Lean_Name_num___override(v___x_208_, v___x_207_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_211_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
v___x_212_ = l_Lean_Name_str___override(v___x_211_, v___x_210_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
v___x_215_ = l_Lean_Name_str___override(v___x_214_, v___x_213_);
return v___x_215_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = lean_unsigned_to_nat(2u);
v___x_217_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
v___x_218_ = l_Lean_Name_num___override(v___x_217_, v___x_216_);
return v___x_218_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_));
v___x_221_ = 1;
v___x_222_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_);
v___x_223_ = l_Lean_registerTraceClass(v___x_220_, v___x_221_, v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_224_;
v_res_224_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_();
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2____boxed(lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_();
return v_res_226_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_));
v___x_247_ = 1;
v___x_248_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_));
v___x_249_ = l_Lean_registerTraceClass(v___x_246_, v___x_247_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_250_;
v_res_250_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_();
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2____boxed(lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_();
return v_res_252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_unsigned_to_nat(2188899847u);
v___x_260_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_261_ = l_Lean_Name_num___override(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_263_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
v___x_264_ = l_Lean_Name_str___override(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
v___x_267_ = l_Lean_Name_str___override(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_unsigned_to_nat(2u);
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
v___x_270_ = l_Lean_Name_num___override(v___x_269_, v___x_268_);
return v___x_270_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_));
v___x_273_ = 1;
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_);
v___x_275_ = l_Lean_registerTraceClass(v___x_272_, v___x_273_, v___x_274_);
return v___x_275_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_276_;
v_res_276_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_();
stack->m_obj
 = v_res_276_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2____boxed(lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_();
return v_res_278_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_));
v___x_300_ = 0;
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_));
v___x_302_ = l_Lean_registerTraceClass(v___x_299_, v___x_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_303_;
v_res_303_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_();
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2____boxed(lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_();
return v_res_305_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_));
v___x_327_ = 1;
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_));
v___x_329_ = l_Lean_registerTraceClass(v___x_326_, v___x_327_, v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_330_;
v_res_330_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_();
stack->m_obj
 = v_res_330_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2____boxed(lean_object* v_a_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_();
return v_res_332_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_));
v___x_354_ = 1;
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_));
v___x_356_ = l_Lean_registerTraceClass(v___x_353_, v___x_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_357_;
v_res_357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_();
stack->m_obj
 = v_res_357_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2____boxed(lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_();
return v_res_359_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_));
v___x_381_ = 1;
v___x_382_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_));
v___x_383_ = l_Lean_registerTraceClass(v___x_380_, v___x_381_, v___x_382_);
return v___x_383_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_384_;
v_res_384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_();
stack->m_obj
 = v_res_384_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2____boxed(lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_();
return v_res_386_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_394_ = lean_unsigned_to_nat(3602332852u);
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_396_ = l_Lean_Name_num___override(v___x_395_, v___x_394_);
return v___x_396_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
v___x_399_ = l_Lean_Name_str___override(v___x_398_, v___x_397_);
return v___x_399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_401_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
v___x_402_ = l_Lean_Name_str___override(v___x_401_, v___x_400_);
return v___x_402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_403_ = lean_unsigned_to_nat(2u);
v___x_404_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
v___x_405_ = l_Lean_Name_num___override(v___x_404_, v___x_403_);
return v___x_405_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_407_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_));
v___x_408_ = 1;
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_);
v___x_410_ = l_Lean_registerTraceClass(v___x_407_, v___x_408_, v___x_409_);
return v___x_410_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_411_;
v_res_411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_();
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2____boxed(lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_();
return v_res_413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(2917960733u);
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__32_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_422_ = l_Lean_Name_num___override(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__34_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
v___x_425_ = l_Lean_Name_str___override(v___x_424_, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__36_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_));
v___x_427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
v___x_428_ = l_Lean_Name_str___override(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_unsigned_to_nat(2u);
v___x_430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
v___x_431_ = l_Lean_Name_num___override(v___x_430_, v___x_429_);
return v___x_431_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_));
v___x_434_ = 0;
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_);
v___x_436_ = l_Lean_registerTraceClass(v___x_433_, v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_437_;
v_res_437_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_();
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2____boxed(lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_();
return v_res_439_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_448_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_449_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_));
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_));
v___x_451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_));
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_));
v___x_453_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_));
v___x_454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_));
v___x_455_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_));
v___x_456_ = l_Lean_Meta_Grind_SolverExtension_setMethods___redArg(v___x_448_, v___x_449_, v___x_450_, v___x_451_, v___x_452_, v___x_453_, v___x_454_, v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_457_;
v_res_457_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_();
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2____boxed(lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_();
return v_res_459_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1977064142____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_864946378____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2867706376____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_273425714____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_118464817____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3761402091____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1769673126____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2188899847____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1878016030____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_356702522____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1398474614____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1427258088____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_3602332852____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_2917960733____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_0__Lean_Meta_Grind_Arith_Linear_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Linear_1206742861____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PropagateEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear(builtin);
}
#ifdef __cplusplus
}
#endif

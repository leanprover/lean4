// Lean compiler output
// Module: Lean.Meta.Tactic.Grind
// Imports: public import Lean.Meta.Tactic.Grind.Attr public import Lean.Meta.Tactic.Grind.RevertAll public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Util public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.Injection public import Lean.Meta.Tactic.Grind.Core public import Lean.Meta.Tactic.Grind.Canon public import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons public import Lean.Meta.Tactic.Grind.Inv public import Lean.Meta.Tactic.Grind.Proof public import Lean.Meta.Tactic.Grind.Propagate public import Lean.Meta.Tactic.Grind.PP public import Lean.Meta.Tactic.Grind.Simp public import Lean.Meta.Tactic.Grind.Ctor public import Lean.Meta.Tactic.Grind.Parser public import Lean.Meta.Tactic.Grind.EMatchTheorem public import Lean.Meta.Tactic.Grind.EMatch public import Lean.Meta.Tactic.Grind.Main public import Lean.Meta.Tactic.Grind.CasesMatch public import Lean.Meta.Tactic.Grind.Arith public import Lean.Meta.Tactic.Grind.Ext public import Lean.Meta.Tactic.Grind.MatchCond public import Lean.Meta.Tactic.Grind.MatchDiscrOnly public import Lean.Meta.Tactic.Grind.Diseq public import Lean.Meta.Tactic.Grind.MBTC public import Lean.Meta.Tactic.Grind.Lookahead public import Lean.Meta.Tactic.Grind.LawfulEqCmp public import Lean.Meta.Tactic.Grind.ReflCmp public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.AC public import Lean.Meta.Tactic.Grind.VarRename public import Lean.Meta.Tactic.Grind.ProofUtil public import Lean.Meta.Tactic.Grind.PropagateInj public import Lean.Meta.Tactic.Grind.Order public import Lean.Meta.Tactic.Grind.Anchor public import Lean.Meta.Tactic.Grind.Action public import Lean.Meta.Tactic.Grind.EMatchTheoremParam public import Lean.Meta.Tactic.Grind.EMatchAction public import Lean.Meta.Tactic.Grind.Filter public import Lean.Meta.Tactic.Grind.CollectParams public import Lean.Meta.Tactic.Grind.Finish public import Lean.Meta.Tactic.Grind.RegisterCommand
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(53, 20, 57, 191, 103, 250, 161, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(32, 62, 18, 58, 32, 75, 174, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 241, 186, 184, 175, 242, 205, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 25, 193, 246, 37, 210, 16, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 208, 99, 105, 65, 145, 25, 148)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 103, 160, 55, 186, 198, 55, 10)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 153, 155, 204, 188, 154, 177, 230)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 15, 251, 89, 200, 108, 127, 8)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(115, 20, 157, 237, 22, 103, 10, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1240498661) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(59, 2, 25, 240, 110, 41, 57, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 166, 24, 121, 182, 41, 16, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 34, 24, 139, 228, 253, 15, 247)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__26_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(125, 197, 245, 102, 153, 230, 233, 41)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 170, 70, 69, 135, 34, 11, 60)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1103938016) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(146, 77, 162, 148, 159, 53, 54, 157)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 199, 243, 148, 250, 55, 122, 133)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 190, 238, 133, 154, 90, 252, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(208, 89, 158, 145, 116, 26, 236, 240)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 181, 250, 47, 64, 71, 92, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(964293774) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(103, 100, 1, 122, 138, 160, 176, 173)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 142, 117, 126, 148, 99, 171, 103)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 6, 60, 197, 82, 9, 178, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(57, 71, 223, 162, 90, 77, 144, 122)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eqc"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 235, 244, 178, 10, 61, 92, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1498262528) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(209, 117, 114, 249, 48, 173, 101, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 110, 131, 181, 43, 102, 157, 71)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(222, 246, 115, 115, 237, 254, 212, 39)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(111, 70, 131, 44, 237, 184, 207, 48)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 70, 251, 102, 13, 158, 236, 64)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ematch"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 181, 7, 237, 157, 224, 161, 99)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "pattern"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 181, 7, 237, 157, 224, 161, 99)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 146, 5, 166, 26, 208, 228, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 181, 7, 237, 157, 224, 161, 99)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 180, 162, 232, 71, 137, 104, 199)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(198996121) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 26, 167, 184, 196, 40, 240, 192)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 87, 120, 117, 255, 221, 150, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 225, 85, 98, 135, 76, 39, 171)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(42, 40, 219, 74, 51, 139, 162, 100)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assignment"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 181, 7, 237, 157, 224, 161, 99)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 180, 162, 232, 71, 137, 104, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(197, 1, 173, 16, 88, 20, 191, 251)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(642649038) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(90, 61, 71, 238, 4, 53, 29, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 154, 192, 200, 41, 107, 228, 234)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 157, 27, 131, 243, 138, 20, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(120, 177, 157, 253, 148, 132, 230, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "delayed"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 181, 7, 237, 157, 224, 161, 99)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 180, 162, 232, 71, 137, 104, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(30, 141, 48, 38, 86, 102, 141, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "eqResolution"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 23, 253, 34, 8, 106, 124, 207)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(89146720) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(212, 238, 229, 0, 197, 198, 232, 100)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 199, 11, 129, 86, 136, 26, 32)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 157, 140, 179, 192, 105, 20, 104)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 121, 98, 200, 41, 72, 116, 52)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "issues"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(2, 26, 246, 148, 197, 20, 141, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 174, 175, 152, 201, 92, 177, 229)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(789062521) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(134, 245, 154, 140, 160, 32, 237, 196)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 223, 31, 174, 255, 80, 88, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 14, 2, 63, 129, 223, 172, 37)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(100, 53, 147, 171, 249, 64, 216, 151)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "split"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 59, 213, 47, 128, 196, 59, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(671723160) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(107, 62, 96, 199, 102, 24, 94, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 89, 8, 206, 0, 52, 223, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 195, 52, 253, 132, 35, 244, 194)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(173, 235, 35, 42, 40, 8, 128, 100)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "candidate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 59, 213, 47, 128, 196, 59, 0)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 75, 202, 223, 191, 4, 135, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(487703842) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(221, 125, 186, 191, 26, 193, 154, 249)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 32, 7, 199, 191, 19, 42, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 212, 183, 108, 60, 162, 39, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(107, 175, 205, 222, 138, 179, 227, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "resolved"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 59, 213, 47, 128, 196, 59, 0)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(121, 117, 87, 107, 170, 21, 173, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "beta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 31, 7, 123, 15, 248, 150, 29)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mbtc"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 58, 101, 243, 41, 236, 253, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ext"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 159, 161, 247, 89, 7, 26, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(189, 159, 161, 247, 89, 7, 26, 174)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 154, 159, 124, 225, 94, 13, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1723019193) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(4, 72, 73, 227, 25, 83, 111, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 100, 82, 200, 69, 240, 56, 108)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(235, 41, 132, 42, 168, 59, 49, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(62, 230, 83, 2, 70, 1, 201, 211)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "lookahead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 254, 220, 45, 238, 117, 220, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 254, 220, 45, 238, 117, 220, 189)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 169, 88, 228, 194, 230, 104, 195)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 254, 220, 45, 238, 117, 220, 189)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 37, 244, 19, 72, 39, 101, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1356401647) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(69, 188, 102, 176, 55, 229, 243, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 251, 51, 236, 120, 177, 133, 63)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(170, 159, 227, 179, 170, 66, 126, 244)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 88, 200, 183, 3, 23, 233, 90)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 254, 220, 45, 238, 117, 220, 189)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 159, 125, 127, 17, 128, 107, 57)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(435833240) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(125, 193, 178, 230, 218, 146, 163, 44)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 132, 189, 239, 169, 89, 32, 74)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 160, 198, 190, 9, 102, 97, 113)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(139, 147, 131, 220, 22, 26, 219, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proofs"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(25, 245, 48, 218, 201, 55, 112, 25)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "congr"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 133, 210, 174, 44, 238, 226, 16)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "proof"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(127, 66, 124, 20, 108, 113, 119, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1713749687) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(59, 125, 155, 65, 53, 66, 75, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 217, 141, 236, 237, 19, 174, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 167, 188, 42, 194, 197, 63, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(125, 46, 132, 254, 24, 221, 90, 174)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 196, 184, 102, 66, 127, 118, 164)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1374249216) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(47, 96, 175, 168, 6, 15, 212, 120)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(36, 48, 32, 112, 133, 83, 188, 162)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(48, 54, 107, 249, 141, 184, 162, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(225, 67, 210, 143, 4, 34, 75, 43)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "parent"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 81, 119, 21, 241, 124, 41, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "final"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 217, 62, 35, 103, 40, 163, 218)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "forallPropagator"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 20, 227, 217, 136, 128, 93, 131)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 217, 152, 239, 89, 139, 148, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(328880924) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(175, 23, 253, 62, 187, 146, 118, 232)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(164, 172, 178, 246, 35, 215, 239, 12)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 44, 233, 241, 240, 109, 166, 92)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(97, 60, 81, 139, 146, 15, 119, 170)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "canon"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 176, 122, 242, 104, 29, 193, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1932954739) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(8, 52, 179, 12, 101, 43, 115, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(47, 181, 47, 56, 139, 179, 177, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(151, 126, 243, 96, 222, 49, 4, 111)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(66, 108, 200, 16, 193, 127, 103, 5)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "activate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(236, 217, 162, 230, 70, 198, 123, 193)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(252, 131, 164, 248, 154, 192, 200, 229)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(904368556) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(176, 162, 162, 152, 244, 75, 61, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 197, 141, 17, 122, 119, 107, 105)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 28, 121, 244, 94, 46, 84, 56)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(170, 137, 41, 235, 57, 144, 72, 51)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 43, 255, 36, 142, 130, 165, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 4, 77, 131, 83, 1, 103, 112)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 64, 101, 181, 200, 140, 42, 219)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(229, 19, 82, 188, 63, 198, 29, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchCond"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1279589469) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(246, 1, 201, 235, 161, 16, 178, 80)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 220, 243, 77, 188, 96, 194, 172)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(105, 123, 163, 37, 22, 5, 174, 116)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(148, 2, 218, 199, 154, 250, 5, 191)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lambda"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(95, 195, 66, 218, 211, 87, 176, 102)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(901832444) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(78, 19, 250, 7, 139, 132, 64, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(153, 76, 192, 14, 16, 102, 188, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(81, 93, 153, 169, 229, 218, 44, 217)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(44, 229, 236, 163, 154, 185, 146, 70)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "proveFalse"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 57, 131, 114, 246, 81, 253, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(6, 3, 200, 238, 83, 121, 101, 214)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(202, 43, 255, 36, 142, 130, 165, 160)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(942114620) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(195, 190, 53, 193, 1, 81, 98, 59)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 141, 123, 242, 17, 201, 140, 18)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(124, 185, 160, 67, 75, 147, 129, 248)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(37, 245, 211, 226, 6, 157, 213, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "proveEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(80, 31, 36, 78, 142, 219, 66, 96)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "pushNewFact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(158, 237, 7, 223, 90, 130, 102, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "appMap"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(134, 13, 183, 192, 24, 201, 133, 201)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 181, 152, 132, 27, 164, 226, 84)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),((lean_object*)(((size_t)(152317745) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(136, 217, 127, 88, 124, 223, 223, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 11, 90, 103, 25, 101, 79, 73)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 87, 209, 111, 33, 123, 42, 128)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(194, 46, 109, 112, 146, 149, 190, 86)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "suggestions"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 118, 163, 105, 194, 26, 61, 26)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "locals"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 141, 181, 10, 83, 129, 93, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_65_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_66_ = 0;
v___x_67_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__27_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_68_ = l_Lean_registerTraceClass(v___x_65_, v___x_66_, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2____boxed(lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_();
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_));
v___x_89_ = 0;
v___x_90_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_));
v___x_91_ = l_Lean_registerTraceClass(v___x_88_, v___x_89_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2____boxed(lean_object* v_a_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_();
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_));
v___x_112_ = 0;
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_));
v___x_114_ = l_Lean_registerTraceClass(v___x_111_, v___x_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2____boxed(lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_();
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_));
v___x_135_ = 0;
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_));
v___x_137_ = l_Lean_registerTraceClass(v___x_134_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2____boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_();
return v_res_139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_unsigned_to_nat(3999206488u);
v___x_145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_146_ = l_Lean_Name_num___override(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_148_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_149_ = l_Lean_Name_str___override(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_151_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_152_ = l_Lean_Name_str___override(v___x_151_, v___x_150_);
return v___x_152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_unsigned_to_nat(2u);
v___x_154_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_155_ = l_Lean_Name_num___override(v___x_154_, v___x_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_));
v___x_158_ = 0;
v___x_159_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_160_ = l_Lean_registerTraceClass(v___x_157_, v___x_158_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2____boxed(lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_();
return v_res_162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_unsigned_to_nat(3083242752u);
v___x_168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_169_ = l_Lean_Name_num___override(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_172_ = l_Lean_Name_str___override(v___x_171_, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_175_ = l_Lean_Name_str___override(v___x_174_, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_unsigned_to_nat(2u);
v___x_177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_178_ = l_Lean_Name_num___override(v___x_177_, v___x_176_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_));
v___x_181_ = 0;
v___x_182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_183_ = l_Lean_registerTraceClass(v___x_180_, v___x_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2____boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_();
return v_res_185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_unsigned_to_nat(2490045716u);
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_193_ = l_Lean_Name_num___override(v___x_192_, v___x_191_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_196_ = l_Lean_Name_str___override(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_199_ = l_Lean_Name_str___override(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = lean_unsigned_to_nat(2u);
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_202_ = l_Lean_Name_num___override(v___x_201_, v___x_200_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_));
v___x_205_ = 0;
v___x_206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_207_ = l_Lean_registerTraceClass(v___x_204_, v___x_205_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2____boxed(lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_228_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_));
v___x_229_ = 0;
v___x_230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_));
v___x_231_ = l_Lean_registerTraceClass(v___x_228_, v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2____boxed(lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_();
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_253_; uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_));
v___x_254_ = 0;
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_));
v___x_256_ = l_Lean_registerTraceClass(v___x_253_, v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2____boxed(lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_();
return v_res_258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_unsigned_to_nat(3198151522u);
v___x_266_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_267_ = l_Lean_Name_num___override(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_269_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_270_ = l_Lean_Name_str___override(v___x_269_, v___x_268_);
return v___x_270_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_273_ = l_Lean_Name_str___override(v___x_272_, v___x_271_);
return v___x_273_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(2u);
v___x_275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_276_ = l_Lean_Name_num___override(v___x_275_, v___x_274_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_));
v___x_279_ = 0;
v___x_280_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_281_ = l_Lean_registerTraceClass(v___x_278_, v___x_279_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2____boxed(lean_object* v_a_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_();
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_));
v___x_302_ = 0;
v___x_303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_));
v___x_304_ = l_Lean_registerTraceClass(v___x_301_, v___x_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2____boxed(lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_();
return v_res_306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_unsigned_to_nat(3281682138u);
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_313_ = l_Lean_Name_num___override(v___x_312_, v___x_311_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_);
v___x_316_ = l_Lean_Name_str___override(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_);
v___x_319_ = l_Lean_Name_str___override(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(2u);
v___x_321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_);
v___x_322_ = l_Lean_Name_num___override(v___x_321_, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_));
v___x_325_ = 0;
v___x_326_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_);
v___x_327_ = l_Lean_registerTraceClass(v___x_324_, v___x_325_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2____boxed(lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_();
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_));
v___x_348_ = 0;
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_));
v___x_350_ = l_Lean_registerTraceClass(v___x_347_, v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2____boxed(lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_370_; uint8_t v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_));
v___x_371_ = 0;
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_));
v___x_373_ = l_Lean_registerTraceClass(v___x_370_, v___x_371_, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2____boxed(lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_394_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_));
v___x_395_ = 0;
v___x_396_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_));
v___x_397_ = l_Lean_registerTraceClass(v___x_394_, v___x_395_, v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2____boxed(lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
return v_res_399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(2208804552u);
v___x_406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_407_ = l_Lean_Name_num___override(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_410_ = l_Lean_Name_str___override(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_413_ = l_Lean_Name_str___override(v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(2u);
v___x_415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_416_ = l_Lean_Name_num___override(v___x_415_, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_));
v___x_419_ = 0;
v___x_420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_421_ = l_Lean_registerTraceClass(v___x_418_, v___x_419_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2____boxed(lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
return v_res_423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_unsigned_to_nat(2239554481u);
v___x_429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_430_ = l_Lean_Name_num___override(v___x_429_, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_433_ = l_Lean_Name_str___override(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_436_ = l_Lean_Name_str___override(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_unsigned_to_nat(2u);
v___x_438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_439_ = l_Lean_Name_num___override(v___x_438_, v___x_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_));
v___x_442_ = 0;
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_444_ = l_Lean_registerTraceClass(v___x_441_, v___x_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
return v_res_446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(2451788450u);
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_453_ = l_Lean_Name_num___override(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_456_ = l_Lean_Name_str___override(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_459_ = l_Lean_Name_str___override(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(2u);
v___x_461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_462_ = l_Lean_Name_num___override(v___x_461_, v___x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_));
v___x_465_ = 0;
v___x_466_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_467_ = l_Lean_registerTraceClass(v___x_464_, v___x_465_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2____boxed(lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
return v_res_469_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = lean_unsigned_to_nat(3390734082u);
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_476_ = l_Lean_Name_num___override(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_479_ = l_Lean_Name_str___override(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_481_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_482_ = l_Lean_Name_str___override(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = lean_unsigned_to_nat(2u);
v___x_484_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_485_ = l_Lean_Name_num___override(v___x_484_, v___x_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_));
v___x_488_ = 0;
v___x_489_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_490_ = l_Lean_registerTraceClass(v___x_487_, v___x_488_, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2____boxed(lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_));
v___x_511_ = 0;
v___x_512_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_));
v___x_513_ = l_Lean_registerTraceClass(v___x_510_, v___x_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2____boxed(lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
return v_res_515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_unsigned_to_nat(2167643761u);
v___x_521_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_522_ = l_Lean_Name_num___override(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_524_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_525_ = l_Lean_Name_str___override(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_527_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_528_ = l_Lean_Name_str___override(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = lean_unsigned_to_nat(2u);
v___x_530_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_531_ = l_Lean_Name_num___override(v___x_530_, v___x_529_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_));
v___x_534_ = 0;
v___x_535_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_536_ = l_Lean_registerTraceClass(v___x_533_, v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2____boxed(lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
return v_res_538_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(3035027224u);
v___x_545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_546_ = l_Lean_Name_num___override(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_549_ = l_Lean_Name_str___override(v___x_548_, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_552_ = l_Lean_Name_str___override(v___x_551_, v___x_550_);
return v___x_552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_unsigned_to_nat(2u);
v___x_554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_555_ = l_Lean_Name_num___override(v___x_554_, v___x_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_));
v___x_558_ = 1;
v___x_559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_560_ = l_Lean_registerTraceClass(v___x_557_, v___x_558_, v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2____boxed(lean_object* v_a_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_));
v___x_582_ = 1;
v___x_583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_));
v___x_584_ = l_Lean_registerTraceClass(v___x_581_, v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2____boxed(lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_));
v___x_605_ = 1;
v___x_606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_));
v___x_607_ = l_Lean_registerTraceClass(v___x_604_, v___x_605_, v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2____boxed(lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
return v_res_609_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_unsigned_to_nat(4253340762u);
v___x_615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_616_ = l_Lean_Name_num___override(v___x_615_, v___x_614_);
return v___x_616_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_619_ = l_Lean_Name_str___override(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_622_ = l_Lean_Name_str___override(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(2u);
v___x_624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_625_ = l_Lean_Name_num___override(v___x_624_, v___x_623_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_627_; uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_));
v___x_628_ = 0;
v___x_629_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_630_ = l_Lean_registerTraceClass(v___x_627_, v___x_628_, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2____boxed(lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
return v_res_632_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(3209233474u);
v___x_639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_640_ = l_Lean_Name_num___override(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_642_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_643_ = l_Lean_Name_str___override(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_646_ = l_Lean_Name_str___override(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_unsigned_to_nat(2u);
v___x_648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_649_ = l_Lean_Name_num___override(v___x_648_, v___x_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_651_; uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_651_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_));
v___x_652_ = 0;
v___x_653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_654_ = l_Lean_registerTraceClass(v___x_651_, v___x_652_, v___x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2____boxed(lean_object* v_a_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
return v_res_656_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(3765097528u);
v___x_663_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_664_ = l_Lean_Name_num___override(v___x_663_, v___x_662_);
return v___x_664_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_666_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_667_ = l_Lean_Name_str___override(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_670_ = l_Lean_Name_str___override(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(2u);
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_673_ = l_Lean_Name_num___override(v___x_672_, v___x_671_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_675_; uint8_t v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_));
v___x_676_ = 0;
v___x_677_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_678_ = l_Lean_registerTraceClass(v___x_675_, v___x_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2____boxed(lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_699_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_));
v___x_700_ = 0;
v___x_701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_));
v___x_702_ = l_Lean_registerTraceClass(v___x_699_, v___x_700_, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2____boxed(lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_723_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_));
v___x_724_ = 0;
v___x_725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_));
v___x_726_ = l_Lean_registerTraceClass(v___x_723_, v___x_724_, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2____boxed(lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
return v_res_728_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(2205948307u);
v___x_735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_736_ = l_Lean_Name_num___override(v___x_735_, v___x_734_);
return v___x_736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_739_ = l_Lean_Name_str___override(v___x_738_, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_742_ = l_Lean_Name_str___override(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_unsigned_to_nat(2u);
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_745_ = l_Lean_Name_num___override(v___x_744_, v___x_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_747_; uint8_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_747_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_));
v___x_748_ = 0;
v___x_749_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_750_ = l_Lean_registerTraceClass(v___x_747_, v___x_748_, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2____boxed(lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
return v_res_752_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_758_ = lean_unsigned_to_nat(3880289020u);
v___x_759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_760_ = l_Lean_Name_num___override(v___x_759_, v___x_758_);
return v___x_760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_763_ = l_Lean_Name_str___override(v___x_762_, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_766_ = l_Lean_Name_str___override(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_unsigned_to_nat(2u);
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_769_ = l_Lean_Name_num___override(v___x_768_, v___x_767_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_));
v___x_772_ = 0;
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_774_ = l_Lean_registerTraceClass(v___x_771_, v___x_772_, v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2____boxed(lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
return v_res_776_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = lean_unsigned_to_nat(3921417167u);
v___x_783_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_784_ = l_Lean_Name_num___override(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_787_ = l_Lean_Name_str___override(v___x_786_, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_790_ = l_Lean_Name_str___override(v___x_789_, v___x_788_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_unsigned_to_nat(2u);
v___x_792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_793_ = l_Lean_Name_num___override(v___x_792_, v___x_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_));
v___x_796_ = 0;
v___x_797_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_798_ = l_Lean_registerTraceClass(v___x_795_, v___x_796_, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2____boxed(lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_818_; uint8_t v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_));
v___x_819_ = 0;
v___x_820_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_));
v___x_821_ = l_Lean_registerTraceClass(v___x_818_, v___x_819_, v___x_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2____boxed(lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_842_; uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_));
v___x_843_ = 0;
v___x_844_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_));
v___x_845_ = l_Lean_registerTraceClass(v___x_842_, v___x_843_, v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2____boxed(lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_));
v___x_869_ = 0;
v___x_870_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_));
v___x_871_ = l_Lean_registerTraceClass(v___x_868_, v___x_869_, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2____boxed(lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
return v_res_873_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = lean_unsigned_to_nat(3036382584u);
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_881_ = l_Lean_Name_num___override(v___x_880_, v___x_879_);
return v___x_881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_883_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_884_ = l_Lean_Name_str___override(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_887_ = l_Lean_Name_str___override(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = lean_unsigned_to_nat(2u);
v___x_889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_890_ = l_Lean_Name_num___override(v___x_889_, v___x_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_892_; uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_892_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_));
v___x_893_ = 0;
v___x_894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_895_ = l_Lean_registerTraceClass(v___x_892_, v___x_893_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2____boxed(lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
return v_res_897_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_unsigned_to_nat(3129348886u);
v___x_903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_904_ = l_Lean_Name_num___override(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_906_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_907_ = l_Lean_Name_str___override(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_910_ = l_Lean_Name_str___override(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = lean_unsigned_to_nat(2u);
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_913_ = l_Lean_Name_num___override(v___x_912_, v___x_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_915_; uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_));
v___x_916_ = 0;
v___x_917_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_918_ = l_Lean_registerTraceClass(v___x_915_, v___x_916_, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2____boxed(lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
return v_res_920_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_unsigned_to_nat(4094675293u);
v___x_926_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_927_ = l_Lean_Name_num___override(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_929_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_930_ = l_Lean_Name_str___override(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_933_ = l_Lean_Name_str___override(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_unsigned_to_nat(2u);
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_936_ = l_Lean_Name_num___override(v___x_935_, v___x_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_938_; uint8_t v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_938_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_));
v___x_939_ = 0;
v___x_940_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_941_ = l_Lean_registerTraceClass(v___x_938_, v___x_939_, v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2____boxed(lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_962_; uint8_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_962_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_));
v___x_963_ = 0;
v___x_964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_));
v___x_965_ = l_Lean_registerTraceClass(v___x_962_, v___x_963_, v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2____boxed(lean_object* v_a_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_987_; uint8_t v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_));
v___x_988_ = 0;
v___x_989_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_));
v___x_990_ = l_Lean_registerTraceClass(v___x_987_, v___x_988_, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2____boxed(lean_object* v_a_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
return v_res_992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_unsigned_to_nat(2833612631u);
v___x_1000_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1001_ = l_Lean_Name_num___override(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1003_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1004_ = l_Lean_Name_str___override(v___x_1003_, v___x_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1006_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1007_ = l_Lean_Name_str___override(v___x_1006_, v___x_1005_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = lean_unsigned_to_nat(2u);
v___x_1009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1010_ = l_Lean_Name_num___override(v___x_1009_, v___x_1008_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1012_; uint8_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_));
v___x_1013_ = 0;
v___x_1014_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1015_ = l_Lean_registerTraceClass(v___x_1012_, v___x_1013_, v___x_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2____boxed(lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
return v_res_1017_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1022_ = lean_unsigned_to_nat(3357376128u);
v___x_1023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1024_ = l_Lean_Name_num___override(v___x_1023_, v___x_1022_);
return v___x_1024_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1027_ = l_Lean_Name_str___override(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1030_ = l_Lean_Name_str___override(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = lean_unsigned_to_nat(2u);
v___x_1032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1033_ = l_Lean_Name_num___override(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_));
v___x_1036_ = 0;
v___x_1037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1038_ = l_Lean_registerTraceClass(v___x_1035_, v___x_1036_, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2____boxed(lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1058_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_));
v___x_1059_ = 0;
v___x_1060_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_));
v___x_1061_ = l_Lean_registerTraceClass(v___x_1058_, v___x_1059_, v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2____boxed(lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
return v_res_1063_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = lean_unsigned_to_nat(3746484445u);
v___x_1070_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1071_ = l_Lean_Name_num___override(v___x_1070_, v___x_1069_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1074_ = l_Lean_Name_str___override(v___x_1073_, v___x_1072_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1077_ = l_Lean_Name_str___override(v___x_1076_, v___x_1075_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = lean_unsigned_to_nat(2u);
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1080_ = l_Lean_Name_num___override(v___x_1079_, v___x_1078_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_));
v___x_1083_ = 0;
v___x_1084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1085_ = l_Lean_registerTraceClass(v___x_1082_, v___x_1083_, v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2____boxed(lean_object* v_a_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
return v_res_1087_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1093_ = lean_unsigned_to_nat(4104889296u);
v___x_1094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1095_ = l_Lean_Name_num___override(v___x_1094_, v___x_1093_);
return v___x_1095_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1097_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1098_ = l_Lean_Name_str___override(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1101_ = l_Lean_Name_str___override(v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_unsigned_to_nat(2u);
v___x_1103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1104_ = l_Lean_Name_num___override(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1106_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_));
v___x_1107_ = 0;
v___x_1108_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1109_ = l_Lean_registerTraceClass(v___x_1106_, v___x_1107_, v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2____boxed(lean_object* v_a_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
return v_res_1111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_unsigned_to_nat(3575722790u);
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1119_ = l_Lean_Name_num___override(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1121_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1122_ = l_Lean_Name_str___override(v___x_1121_, v___x_1120_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1125_ = l_Lean_Name_str___override(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_unsigned_to_nat(2u);
v___x_1127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1128_ = l_Lean_Name_num___override(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v___x_1130_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_));
v___x_1131_ = 0;
v___x_1132_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1133_ = l_Lean_registerTraceClass(v___x_1130_, v___x_1131_, v___x_1132_);
return v___x_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2____boxed(lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_));
v___x_1154_ = 0;
v___x_1155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_));
v___x_1156_ = l_Lean_registerTraceClass(v___x_1153_, v___x_1154_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2____boxed(lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
return v_res_1158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_unsigned_to_nat(2489964793u);
v___x_1165_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1166_ = l_Lean_Name_num___override(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1168_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1169_ = l_Lean_Name_str___override(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1172_ = l_Lean_Name_str___override(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_unsigned_to_nat(2u);
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1175_ = l_Lean_Name_num___override(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1177_; uint8_t v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_));
v___x_1178_ = 0;
v___x_1179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1180_ = l_Lean_registerTraceClass(v___x_1177_, v___x_1178_, v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2____boxed(lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
return v_res_1182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1188_ = lean_unsigned_to_nat(2691769277u);
v___x_1189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1190_ = l_Lean_Name_num___override(v___x_1189_, v___x_1188_);
return v___x_1190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1193_ = l_Lean_Name_str___override(v___x_1192_, v___x_1191_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1196_ = l_Lean_Name_str___override(v___x_1195_, v___x_1194_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_unsigned_to_nat(2u);
v___x_1198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1199_ = l_Lean_Name_num___override(v___x_1198_, v___x_1197_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_));
v___x_1202_ = 0;
v___x_1203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1204_ = l_Lean_registerTraceClass(v___x_1201_, v___x_1202_, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2____boxed(lean_object* v_a_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
return v_res_1206_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ReflCmp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Order(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3281682138____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Canon(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PP(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Parser(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatch(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Ext(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Diseq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MBTC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Lookahead(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ReflCmp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_AC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ProofUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagateInj(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Order(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Canon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Inv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PP(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ctor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MBTC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Lookahead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_LawfulEqCmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ProofUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagateInj(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EMatchAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Filter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CollectParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Finish(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_RegisterCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind(builtin);
}
#ifdef __cplusplus
}
#endif

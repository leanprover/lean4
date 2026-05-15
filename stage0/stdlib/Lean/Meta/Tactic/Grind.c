// Lean compiler output
// Module: Lean.Meta.Tactic.Grind
// Imports: public import Lean.Meta.Tactic.Grind.Attr public import Lean.Meta.Tactic.Grind.RevertAll public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Util public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.Injection public import Lean.Meta.Tactic.Grind.Core public import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons public import Lean.Meta.Tactic.Grind.Inv public import Lean.Meta.Tactic.Grind.Proof public import Lean.Meta.Tactic.Grind.Propagate public import Lean.Meta.Tactic.Grind.PP public import Lean.Meta.Tactic.Grind.Simp public import Lean.Meta.Tactic.Grind.Ctor public import Lean.Meta.Tactic.Grind.Parser public import Lean.Meta.Tactic.Grind.EMatchTheorem public import Lean.Meta.Tactic.Grind.EMatch public import Lean.Meta.Tactic.Grind.Main public import Lean.Meta.Tactic.Grind.CasesMatch public import Lean.Meta.Tactic.Grind.Arith public import Lean.Meta.Tactic.Grind.Ext public import Lean.Meta.Tactic.Grind.MatchCond public import Lean.Meta.Tactic.Grind.MatchDiscrOnly public import Lean.Meta.Tactic.Grind.Diseq public import Lean.Meta.Tactic.Grind.MBTC public import Lean.Meta.Tactic.Grind.Lookahead public import Lean.Meta.Tactic.Grind.LawfulEqCmp public import Lean.Meta.Tactic.Grind.ReflCmp public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.AC public import Lean.Meta.Tactic.Grind.VarRename public import Lean.Meta.Tactic.Grind.ProofUtil public import Lean.Meta.Tactic.Grind.PropagateInj public import Lean.Meta.Tactic.Grind.Order public import Lean.Meta.Tactic.Grind.Anchor public import Lean.Meta.Tactic.Grind.Action public import Lean.Meta.Tactic.Grind.EMatchTheoremParam public import Lean.Meta.Tactic.Grind.EMatchAction public import Lean.Meta.Tactic.Grind.Filter public import Lean.Meta.Tactic.Grind.CollectParams public import Lean.Meta.Tactic.Grind.Finish public import Lean.Meta.Tactic.Grind.RegisterCommand
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "diagnostics"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 181, 7, 237, 157, 224, 161, 99)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 49, 15, 151, 234, 106, 64, 51)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 117, 127, 207, 57, 37, 255, 126)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_));
v___x_325_ = 0;
v___x_326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_));
v___x_327_ = l_Lean_registerTraceClass(v___x_324_, v___x_325_, v___x_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2____boxed(lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_));
v___x_348_ = 0;
v___x_349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_));
v___x_350_ = l_Lean_registerTraceClass(v___x_347_, v___x_348_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2____boxed(lean_object* v_a_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_));
v___x_372_ = 0;
v___x_373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_));
v___x_374_ = l_Lean_registerTraceClass(v___x_371_, v___x_372_, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2____boxed(lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
return v_res_376_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_unsigned_to_nat(2208804552u);
v___x_383_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_384_ = l_Lean_Name_num___override(v___x_383_, v___x_382_);
return v___x_384_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_387_ = l_Lean_Name_str___override(v___x_386_, v___x_385_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_390_ = l_Lean_Name_str___override(v___x_389_, v___x_388_);
return v___x_390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = lean_unsigned_to_nat(2u);
v___x_392_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_393_ = l_Lean_Name_num___override(v___x_392_, v___x_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_));
v___x_396_ = 0;
v___x_397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_398_ = l_Lean_registerTraceClass(v___x_395_, v___x_396_, v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2____boxed(lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
return v_res_400_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(2239554481u);
v___x_406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_407_ = l_Lean_Name_num___override(v___x_406_, v___x_405_);
return v___x_407_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_410_ = l_Lean_Name_str___override(v___x_409_, v___x_408_);
return v___x_410_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_412_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_413_ = l_Lean_Name_str___override(v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_unsigned_to_nat(2u);
v___x_415_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_416_ = l_Lean_Name_num___override(v___x_415_, v___x_414_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_));
v___x_419_ = 0;
v___x_420_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_421_ = l_Lean_registerTraceClass(v___x_418_, v___x_419_, v___x_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2____boxed(lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
return v_res_423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_unsigned_to_nat(2451788450u);
v___x_429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_430_ = l_Lean_Name_num___override(v___x_429_, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_433_ = l_Lean_Name_str___override(v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_436_ = l_Lean_Name_str___override(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_unsigned_to_nat(2u);
v___x_438_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_439_ = l_Lean_Name_num___override(v___x_438_, v___x_437_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_));
v___x_442_ = 0;
v___x_443_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_444_ = l_Lean_registerTraceClass(v___x_441_, v___x_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
return v_res_446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_451_ = lean_unsigned_to_nat(3390734082u);
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_453_ = l_Lean_Name_num___override(v___x_452_, v___x_451_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_455_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_456_ = l_Lean_Name_str___override(v___x_455_, v___x_454_);
return v___x_456_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_458_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_459_ = l_Lean_Name_str___override(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(2u);
v___x_461_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_462_ = l_Lean_Name_num___override(v___x_461_, v___x_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_464_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_));
v___x_465_ = 0;
v___x_466_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_467_ = l_Lean_registerTraceClass(v___x_464_, v___x_465_, v___x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2____boxed(lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_));
v___x_488_ = 0;
v___x_489_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_));
v___x_490_ = l_Lean_registerTraceClass(v___x_487_, v___x_488_, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2____boxed(lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
return v_res_492_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(2167643761u);
v___x_498_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_499_ = l_Lean_Name_num___override(v___x_498_, v___x_497_);
return v___x_499_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_501_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_502_ = l_Lean_Name_str___override(v___x_501_, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_504_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_505_ = l_Lean_Name_str___override(v___x_504_, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = lean_unsigned_to_nat(2u);
v___x_507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_508_ = l_Lean_Name_num___override(v___x_507_, v___x_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_510_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_));
v___x_511_ = 0;
v___x_512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_513_ = l_Lean_registerTraceClass(v___x_510_, v___x_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2____boxed(lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
return v_res_515_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = lean_unsigned_to_nat(3035027224u);
v___x_522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_523_ = l_Lean_Name_num___override(v___x_522_, v___x_521_);
return v___x_523_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_524_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_526_ = l_Lean_Name_str___override(v___x_525_, v___x_524_);
return v___x_526_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_529_ = l_Lean_Name_str___override(v___x_528_, v___x_527_);
return v___x_529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_unsigned_to_nat(2u);
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_532_ = l_Lean_Name_num___override(v___x_531_, v___x_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_534_; uint8_t v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_));
v___x_535_ = 1;
v___x_536_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_537_ = l_Lean_registerTraceClass(v___x_534_, v___x_535_, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2____boxed(lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_558_; uint8_t v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_));
v___x_559_ = 1;
v___x_560_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_));
v___x_561_ = l_Lean_registerTraceClass(v___x_558_, v___x_559_, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2____boxed(lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_581_; uint8_t v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_));
v___x_582_ = 1;
v___x_583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_));
v___x_584_ = l_Lean_registerTraceClass(v___x_581_, v___x_582_, v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2____boxed(lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
return v_res_586_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = lean_unsigned_to_nat(3832561742u);
v___x_595_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_596_ = l_Lean_Name_num___override(v___x_595_, v___x_594_);
return v___x_596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_598_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_599_ = l_Lean_Name_str___override(v___x_598_, v___x_597_);
return v___x_599_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_600_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_601_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_602_ = l_Lean_Name_str___override(v___x_601_, v___x_600_);
return v___x_602_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(2u);
v___x_604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_605_ = l_Lean_Name_num___override(v___x_604_, v___x_603_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_));
v___x_608_ = 0;
v___x_609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_610_ = l_Lean_registerTraceClass(v___x_607_, v___x_608_, v___x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2____boxed(lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_();
return v_res_612_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_unsigned_to_nat(4253340762u);
v___x_618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_619_ = l_Lean_Name_num___override(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_622_ = l_Lean_Name_str___override(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_625_ = l_Lean_Name_str___override(v___x_624_, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(2u);
v___x_627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_628_ = l_Lean_Name_num___override(v___x_627_, v___x_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_));
v___x_631_ = 0;
v___x_632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_633_ = l_Lean_registerTraceClass(v___x_630_, v___x_631_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2____boxed(lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
return v_res_635_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_unsigned_to_nat(3209233474u);
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_643_ = l_Lean_Name_num___override(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_646_ = l_Lean_Name_str___override(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_649_ = l_Lean_Name_str___override(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(2u);
v___x_651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_652_ = l_Lean_Name_num___override(v___x_651_, v___x_650_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_));
v___x_655_ = 0;
v___x_656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_657_ = l_Lean_registerTraceClass(v___x_654_, v___x_655_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2____boxed(lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
return v_res_659_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_unsigned_to_nat(3765097528u);
v___x_666_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_667_ = l_Lean_Name_num___override(v___x_666_, v___x_665_);
return v___x_667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_669_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_670_ = l_Lean_Name_str___override(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_672_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_673_ = l_Lean_Name_str___override(v___x_672_, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(2u);
v___x_675_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_676_ = l_Lean_Name_num___override(v___x_675_, v___x_674_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_678_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_));
v___x_679_ = 0;
v___x_680_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_681_ = l_Lean_registerTraceClass(v___x_678_, v___x_679_, v___x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2____boxed(lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_));
v___x_703_ = 0;
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_));
v___x_705_ = l_Lean_registerTraceClass(v___x_702_, v___x_703_, v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2____boxed(lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_));
v___x_727_ = 0;
v___x_728_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_));
v___x_729_ = l_Lean_registerTraceClass(v___x_726_, v___x_727_, v___x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2____boxed(lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
return v_res_731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_737_ = lean_unsigned_to_nat(2205948307u);
v___x_738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_739_ = l_Lean_Name_num___override(v___x_738_, v___x_737_);
return v___x_739_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_741_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_742_ = l_Lean_Name_str___override(v___x_741_, v___x_740_);
return v___x_742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_745_ = l_Lean_Name_str___override(v___x_744_, v___x_743_);
return v___x_745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(2u);
v___x_747_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_748_ = l_Lean_Name_num___override(v___x_747_, v___x_746_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_));
v___x_751_ = 0;
v___x_752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_753_ = l_Lean_registerTraceClass(v___x_750_, v___x_751_, v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2____boxed(lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
return v_res_755_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_761_ = lean_unsigned_to_nat(3880289020u);
v___x_762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_763_ = l_Lean_Name_num___override(v___x_762_, v___x_761_);
return v___x_763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_766_ = l_Lean_Name_str___override(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_768_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_769_ = l_Lean_Name_str___override(v___x_768_, v___x_767_);
return v___x_769_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_unsigned_to_nat(2u);
v___x_771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_772_ = l_Lean_Name_num___override(v___x_771_, v___x_770_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_774_; uint8_t v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_));
v___x_775_ = 0;
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_777_ = l_Lean_registerTraceClass(v___x_774_, v___x_775_, v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2____boxed(lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
return v_res_779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_unsigned_to_nat(3921417167u);
v___x_786_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_787_ = l_Lean_Name_num___override(v___x_786_, v___x_785_);
return v___x_787_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_788_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_789_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_790_ = l_Lean_Name_str___override(v___x_789_, v___x_788_);
return v___x_790_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_792_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_793_ = l_Lean_Name_str___override(v___x_792_, v___x_791_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(2u);
v___x_795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_796_ = l_Lean_Name_num___override(v___x_795_, v___x_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_));
v___x_799_ = 0;
v___x_800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_801_ = l_Lean_registerTraceClass(v___x_798_, v___x_799_, v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2____boxed(lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_));
v___x_822_ = 0;
v___x_823_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_));
v___x_824_ = l_Lean_registerTraceClass(v___x_821_, v___x_822_, v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2____boxed(lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_845_; uint8_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_845_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_));
v___x_846_ = 0;
v___x_847_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_));
v___x_848_ = l_Lean_registerTraceClass(v___x_845_, v___x_846_, v___x_847_);
return v___x_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2____boxed(lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_871_; uint8_t v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_));
v___x_872_ = 0;
v___x_873_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_));
v___x_874_ = l_Lean_registerTraceClass(v___x_871_, v___x_872_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2____boxed(lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
return v_res_876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_882_ = lean_unsigned_to_nat(3036382584u);
v___x_883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_884_ = l_Lean_Name_num___override(v___x_883_, v___x_882_);
return v___x_884_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_886_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_887_ = l_Lean_Name_str___override(v___x_886_, v___x_885_);
return v___x_887_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_888_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_889_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_890_ = l_Lean_Name_str___override(v___x_889_, v___x_888_);
return v___x_890_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = lean_unsigned_to_nat(2u);
v___x_892_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_893_ = l_Lean_Name_num___override(v___x_892_, v___x_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_895_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_));
v___x_896_ = 0;
v___x_897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_898_ = l_Lean_registerTraceClass(v___x_895_, v___x_896_, v___x_897_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2____boxed(lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
return v_res_900_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_unsigned_to_nat(3129348886u);
v___x_906_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_907_ = l_Lean_Name_num___override(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_909_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_910_ = l_Lean_Name_str___override(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_913_ = l_Lean_Name_str___override(v___x_912_, v___x_911_);
return v___x_913_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = lean_unsigned_to_nat(2u);
v___x_915_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_916_ = l_Lean_Name_num___override(v___x_915_, v___x_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_918_; uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_));
v___x_919_ = 0;
v___x_920_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_921_ = l_Lean_registerTraceClass(v___x_918_, v___x_919_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2____boxed(lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
return v_res_923_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_unsigned_to_nat(4094675293u);
v___x_929_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_930_ = l_Lean_Name_num___override(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_933_ = l_Lean_Name_str___override(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_936_ = l_Lean_Name_str___override(v___x_935_, v___x_934_);
return v___x_936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_937_ = lean_unsigned_to_nat(2u);
v___x_938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_939_ = l_Lean_Name_num___override(v___x_938_, v___x_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_941_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_));
v___x_942_ = 0;
v___x_943_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_944_ = l_Lean_registerTraceClass(v___x_941_, v___x_942_, v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2____boxed(lean_object* v_a_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_965_; uint8_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_));
v___x_966_ = 0;
v___x_967_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_));
v___x_968_ = l_Lean_registerTraceClass(v___x_965_, v___x_966_, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2____boxed(lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_));
v___x_991_ = 0;
v___x_992_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_));
v___x_993_ = l_Lean_registerTraceClass(v___x_990_, v___x_991_, v___x_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2____boxed(lean_object* v_a_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
return v_res_995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_unsigned_to_nat(2833612631u);
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1004_ = l_Lean_Name_num___override(v___x_1003_, v___x_1002_);
return v___x_1004_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1006_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1007_ = l_Lean_Name_str___override(v___x_1006_, v___x_1005_);
return v___x_1007_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1008_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1009_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1010_ = l_Lean_Name_str___override(v___x_1009_, v___x_1008_);
return v___x_1010_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = lean_unsigned_to_nat(2u);
v___x_1012_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1013_ = l_Lean_Name_num___override(v___x_1012_, v___x_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1015_; uint8_t v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_));
v___x_1016_ = 0;
v___x_1017_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1018_ = l_Lean_registerTraceClass(v___x_1015_, v___x_1016_, v___x_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2____boxed(lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
return v_res_1020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1025_ = lean_unsigned_to_nat(3357376128u);
v___x_1026_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1027_ = l_Lean_Name_num___override(v___x_1026_, v___x_1025_);
return v___x_1027_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1030_ = l_Lean_Name_str___override(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1032_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1033_ = l_Lean_Name_str___override(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_unsigned_to_nat(2u);
v___x_1035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1036_ = l_Lean_Name_num___override(v___x_1035_, v___x_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1038_; uint8_t v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_));
v___x_1039_ = 0;
v___x_1040_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1041_ = l_Lean_registerTraceClass(v___x_1038_, v___x_1039_, v___x_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2____boxed(lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1061_; uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_));
v___x_1062_ = 0;
v___x_1063_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_));
v___x_1064_ = l_Lean_registerTraceClass(v___x_1061_, v___x_1062_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2____boxed(lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
return v_res_1066_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = lean_unsigned_to_nat(3746484445u);
v___x_1073_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1074_ = l_Lean_Name_num___override(v___x_1073_, v___x_1072_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1077_ = l_Lean_Name_str___override(v___x_1076_, v___x_1075_);
return v___x_1077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1079_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1080_ = l_Lean_Name_str___override(v___x_1079_, v___x_1078_);
return v___x_1080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_unsigned_to_nat(2u);
v___x_1082_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1083_ = l_Lean_Name_num___override(v___x_1082_, v___x_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1085_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_));
v___x_1086_ = 0;
v___x_1087_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1088_ = l_Lean_registerTraceClass(v___x_1085_, v___x_1086_, v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2____boxed(lean_object* v_a_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
return v_res_1090_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v___x_1096_ = lean_unsigned_to_nat(4104889296u);
v___x_1097_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1098_ = l_Lean_Name_num___override(v___x_1097_, v___x_1096_);
return v___x_1098_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1101_ = l_Lean_Name_str___override(v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1103_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1104_ = l_Lean_Name_str___override(v___x_1103_, v___x_1102_);
return v___x_1104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_unsigned_to_nat(2u);
v___x_1106_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1107_ = l_Lean_Name_num___override(v___x_1106_, v___x_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1109_; uint8_t v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_));
v___x_1110_ = 0;
v___x_1111_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1112_ = l_Lean_registerTraceClass(v___x_1109_, v___x_1110_, v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2____boxed(lean_object* v_a_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
return v_res_1114_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = lean_unsigned_to_nat(3575722790u);
v___x_1121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1122_ = l_Lean_Name_num___override(v___x_1121_, v___x_1120_);
return v___x_1122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1124_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1125_ = l_Lean_Name_str___override(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1127_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1128_ = l_Lean_Name_str___override(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_unsigned_to_nat(2u);
v___x_1130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1131_ = l_Lean_Name_num___override(v___x_1130_, v___x_1129_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1133_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_));
v___x_1134_ = 0;
v___x_1135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1136_ = l_Lean_registerTraceClass(v___x_1133_, v___x_1134_, v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2____boxed(lean_object* v_a_1137_){
_start:
{
lean_object* v_res_1138_; 
v_res_1138_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_));
v___x_1157_ = 0;
v___x_1158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_));
v___x_1159_ = l_Lean_registerTraceClass(v___x_1156_, v___x_1157_, v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2____boxed(lean_object* v_a_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
return v_res_1161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1167_ = lean_unsigned_to_nat(2489964793u);
v___x_1168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1169_ = l_Lean_Name_num___override(v___x_1168_, v___x_1167_);
return v___x_1169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1172_ = l_Lean_Name_str___override(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1175_ = l_Lean_Name_str___override(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_unsigned_to_nat(2u);
v___x_1177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1178_ = l_Lean_Name_num___override(v___x_1177_, v___x_1176_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1180_; uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_));
v___x_1181_ = 0;
v___x_1182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1183_ = l_Lean_registerTraceClass(v___x_1180_, v___x_1181_, v___x_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2____boxed(lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
return v_res_1185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(2691769277u);
v___x_1192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1193_ = l_Lean_Name_num___override(v___x_1192_, v___x_1191_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1195_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1196_ = l_Lean_Name_str___override(v___x_1195_, v___x_1194_);
return v___x_1196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1199_ = l_Lean_Name_str___override(v___x_1198_, v___x_1197_);
return v___x_1199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1200_ = lean_unsigned_to_nat(2u);
v___x_1201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1202_ = l_Lean_Name_num___override(v___x_1201_, v___x_1200_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_));
v___x_1205_ = 0;
v___x_1206_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1207_ = l_Lean_registerTraceClass(v___x_1204_, v___x_1205_, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2____boxed(lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
return v_res_1209_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
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
res = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_();
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

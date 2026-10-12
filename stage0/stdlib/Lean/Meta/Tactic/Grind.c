// Lean compiler output
// Module: Lean.Meta.Tactic.Grind
// Imports: public import Lean.Meta.Tactic.Grind.Attr public import Lean.Meta.Tactic.Grind.MarkAccessible public import Lean.Meta.Tactic.Grind.Types public import Lean.Meta.Tactic.Grind.Util public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.Injection public import Lean.Meta.Tactic.Grind.Core public import Lean.Meta.Tactic.Grind.MarkNestedSubsingletons public import Lean.Meta.Tactic.Grind.Inv public import Lean.Meta.Tactic.Grind.Proof public import Lean.Meta.Tactic.Grind.Propagate public import Lean.Meta.Tactic.Grind.PropagateChar public import Lean.Meta.Tactic.Grind.BitVec public import Lean.Meta.Tactic.Grind.PP public import Lean.Meta.Tactic.Grind.Simp public import Lean.Meta.Tactic.Grind.Ctor public import Lean.Meta.Tactic.Grind.Parser public import Lean.Meta.Tactic.Grind.EMatchTheorem public import Lean.Meta.Tactic.Grind.EMatch public import Lean.Meta.Tactic.Grind.Main public import Lean.Meta.Tactic.Grind.CasesMatch public import Lean.Meta.Tactic.Grind.Arith public import Lean.Meta.Tactic.Grind.Ext public import Lean.Meta.Tactic.Grind.MatchCond public import Lean.Meta.Tactic.Grind.MatchDiscrOnly public import Lean.Meta.Tactic.Grind.Diseq public import Lean.Meta.Tactic.Grind.MBTC public import Lean.Meta.Tactic.Grind.Lookahead public import Lean.Meta.Tactic.Grind.LawfulEqCmp public import Lean.Meta.Tactic.Grind.ReflCmp public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.AC public import Lean.Meta.Tactic.Grind.VarRename public import Lean.Meta.Tactic.Grind.ProofUtil public import Lean.Meta.Tactic.Grind.PropagateInj public import Lean.Meta.Tactic.Grind.Order public import Lean.Meta.Tactic.Grind.Homomorphism public import Lean.Meta.Tactic.Grind.Anchor public import Lean.Meta.Tactic.Grind.Action public import Lean.Meta.Tactic.Grind.EMatchTheoremParam public import Lean.Meta.Tactic.Grind.EMatchAction public import Lean.Meta.Tactic.Grind.Filter public import Lean.Meta.Tactic.Grind.CollectParams public import Lean.Meta.Tactic.Grind.Finish public import Lean.Meta.Tactic.Grind.RegisterCommand public import Lean.Meta.Tactic.Grind.BVDecide
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
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_(){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_();
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2____boxed(lean_object* v_a_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_();
return v_res_71_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_));
v___x_90_ = 0;
v___x_91_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_));
v___x_92_ = l_Lean_registerTraceClass(v___x_89_, v___x_90_, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_93_;
v_res_93_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_();
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2____boxed(lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1103938016____hygCtx___hyg_2_();
return v_res_95_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_));
v___x_114_ = 0;
v___x_115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_));
v___x_116_ = l_Lean_registerTraceClass(v___x_113_, v___x_114_, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_117_;
v_res_117_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_();
stack->m_obj
 = v_res_117_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2____boxed(lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_964293774____hygCtx___hyg_2_();
return v_res_119_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_137_; uint8_t v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_));
v___x_138_ = 0;
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_));
v___x_140_ = l_Lean_registerTraceClass(v___x_137_, v___x_138_, v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_141_;
v_res_141_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_();
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2____boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1498262528____hygCtx___hyg_2_();
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(3999206488u);
v___x_149_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_150_ = l_Lean_Name_num___override(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_152_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_153_ = l_Lean_Name_str___override(v___x_152_, v___x_151_);
return v___x_153_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_156_ = l_Lean_Name_str___override(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_159_ = l_Lean_Name_num___override(v___x_158_, v___x_157_);
return v___x_159_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_));
v___x_162_ = 0;
v___x_163_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_);
v___x_164_ = l_Lean_registerTraceClass(v___x_161_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_165_;
v_res_165_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_();
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2____boxed(lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3999206488____hygCtx___hyg_2_();
return v_res_167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_unsigned_to_nat(3083242752u);
v___x_173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_174_ = l_Lean_Name_num___override(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_177_ = l_Lean_Name_str___override(v___x_176_, v___x_175_);
return v___x_177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_180_ = l_Lean_Name_str___override(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_unsigned_to_nat(2u);
v___x_182_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_183_ = l_Lean_Name_num___override(v___x_182_, v___x_181_);
return v___x_183_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_185_; uint8_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_));
v___x_186_ = 0;
v___x_187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_);
v___x_188_ = l_Lean_registerTraceClass(v___x_185_, v___x_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_189_;
v_res_189_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_();
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2____boxed(lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3083242752____hygCtx___hyg_2_();
return v_res_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_unsigned_to_nat(2490045716u);
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_199_ = l_Lean_Name_num___override(v___x_198_, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_202_ = l_Lean_Name_str___override(v___x_201_, v___x_200_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_205_ = l_Lean_Name_str___override(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_unsigned_to_nat(2u);
v___x_207_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_208_ = l_Lean_Name_num___override(v___x_207_, v___x_206_);
return v___x_208_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_));
v___x_211_ = 0;
v___x_212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_);
v___x_213_ = l_Lean_registerTraceClass(v___x_210_, v___x_211_, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_214_;
v_res_214_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_();
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2____boxed(lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2490045716____hygCtx___hyg_2_();
return v_res_216_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_));
v___x_236_ = 0;
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_));
v___x_238_ = l_Lean_registerTraceClass(v___x_235_, v___x_236_, v___x_237_);
return v___x_238_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_239_;
v_res_239_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_();
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2____boxed(lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_198996121____hygCtx___hyg_2_();
return v_res_241_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_));
v___x_262_ = 0;
v___x_263_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_));
v___x_264_ = l_Lean_registerTraceClass(v___x_261_, v___x_262_, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_265_;
v_res_265_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_();
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2____boxed(lean_object* v_a_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_642649038____hygCtx___hyg_2_();
return v_res_267_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_unsigned_to_nat(3198151522u);
v___x_275_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_276_ = l_Lean_Name_num___override(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_279_ = l_Lean_Name_str___override(v___x_278_, v___x_277_);
return v___x_279_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_282_ = l_Lean_Name_str___override(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_unsigned_to_nat(2u);
v___x_284_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_285_ = l_Lean_Name_num___override(v___x_284_, v___x_283_);
return v___x_285_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_));
v___x_288_ = 0;
v___x_289_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_);
v___x_290_ = l_Lean_registerTraceClass(v___x_287_, v___x_288_, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_291_;
v_res_291_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_();
stack->m_obj
 = v_res_291_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2____boxed(lean_object* v_a_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3198151522____hygCtx___hyg_2_();
return v_res_293_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_));
v___x_312_ = 0;
v___x_313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_));
v___x_314_ = l_Lean_registerTraceClass(v___x_311_, v___x_312_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_315_;
v_res_315_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_();
stack->m_obj
 = v_res_315_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2____boxed(lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_89146720____hygCtx___hyg_2_();
return v_res_317_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_));
v___x_336_ = 0;
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_));
v___x_338_ = l_Lean_registerTraceClass(v___x_335_, v___x_336_, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_339_;
v_res_339_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2____boxed(lean_object* v_a_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_789062521____hygCtx___hyg_2_();
return v_res_341_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_));
v___x_360_ = 0;
v___x_361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_));
v___x_362_ = l_Lean_registerTraceClass(v___x_359_, v___x_360_, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_363_;
v_res_363_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2____boxed(lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_671723160____hygCtx___hyg_2_();
return v_res_365_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_));
v___x_385_ = 0;
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_));
v___x_387_ = l_Lean_registerTraceClass(v___x_384_, v___x_385_, v___x_386_);
return v___x_387_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_388_;
v_res_388_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
stack->m_obj
 = v_res_388_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2____boxed(lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_487703842____hygCtx___hyg_2_();
return v_res_390_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_396_ = lean_unsigned_to_nat(2208804552u);
v___x_397_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_398_ = l_Lean_Name_num___override(v___x_397_, v___x_396_);
return v___x_398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_399_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_400_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_401_ = l_Lean_Name_str___override(v___x_400_, v___x_399_);
return v___x_401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_403_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_404_ = l_Lean_Name_str___override(v___x_403_, v___x_402_);
return v___x_404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_405_ = lean_unsigned_to_nat(2u);
v___x_406_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_407_ = l_Lean_Name_num___override(v___x_406_, v___x_405_);
return v___x_407_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_));
v___x_410_ = 0;
v___x_411_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_);
v___x_412_ = l_Lean_registerTraceClass(v___x_409_, v___x_410_, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_413_;
v_res_413_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2____boxed(lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2208804552____hygCtx___hyg_2_();
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_unsigned_to_nat(2239554481u);
v___x_421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_422_ = l_Lean_Name_num___override(v___x_421_, v___x_420_);
return v___x_422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_425_ = l_Lean_Name_str___override(v___x_424_, v___x_423_);
return v___x_425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_427_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_428_ = l_Lean_Name_str___override(v___x_427_, v___x_426_);
return v___x_428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_unsigned_to_nat(2u);
v___x_430_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_431_ = l_Lean_Name_num___override(v___x_430_, v___x_429_);
return v___x_431_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_433_; uint8_t v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_));
v___x_434_ = 0;
v___x_435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_);
v___x_436_ = l_Lean_registerTraceClass(v___x_433_, v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_437_;
v_res_437_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
stack->m_obj
 = v_res_437_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2____boxed(lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2239554481____hygCtx___hyg_2_();
return v_res_439_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = lean_unsigned_to_nat(2451788450u);
v___x_445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_446_ = l_Lean_Name_num___override(v___x_445_, v___x_444_);
return v___x_446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_449_ = l_Lean_Name_str___override(v___x_448_, v___x_447_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_452_ = l_Lean_Name_str___override(v___x_451_, v___x_450_);
return v___x_452_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_unsigned_to_nat(2u);
v___x_454_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_455_ = l_Lean_Name_num___override(v___x_454_, v___x_453_);
return v___x_455_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_457_; uint8_t v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_457_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_));
v___x_458_ = 0;
v___x_459_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_);
v___x_460_ = l_Lean_registerTraceClass(v___x_457_, v___x_458_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_461_;
v_res_461_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2____boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2451788450____hygCtx___hyg_2_();
return v_res_463_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = lean_unsigned_to_nat(3390734082u);
v___x_469_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_470_ = l_Lean_Name_num___override(v___x_469_, v___x_468_);
return v___x_470_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_472_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_473_ = l_Lean_Name_str___override(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_475_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_476_ = l_Lean_Name_str___override(v___x_475_, v___x_474_);
return v___x_476_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_unsigned_to_nat(2u);
v___x_478_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_479_ = l_Lean_Name_num___override(v___x_478_, v___x_477_);
return v___x_479_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_));
v___x_482_ = 0;
v___x_483_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_);
v___x_484_ = l_Lean_registerTraceClass(v___x_481_, v___x_482_, v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_485_;
v_res_485_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
stack->m_obj
 = v_res_485_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2____boxed(lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3390734082____hygCtx___hyg_2_();
return v_res_487_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_));
v___x_506_ = 0;
v___x_507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_));
v___x_508_ = l_Lean_registerTraceClass(v___x_505_, v___x_506_, v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_509_;
v_res_509_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2____boxed(lean_object* v_a_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1723019193____hygCtx___hyg_2_();
return v_res_511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_516_ = lean_unsigned_to_nat(2167643761u);
v___x_517_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_518_ = l_Lean_Name_num___override(v___x_517_, v___x_516_);
return v___x_518_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_521_ = l_Lean_Name_str___override(v___x_520_, v___x_519_);
return v___x_521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_524_ = l_Lean_Name_str___override(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_527_ = l_Lean_Name_num___override(v___x_526_, v___x_525_);
return v___x_527_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_529_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_));
v___x_530_ = 0;
v___x_531_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_);
v___x_532_ = l_Lean_registerTraceClass(v___x_529_, v___x_530_, v___x_531_);
return v___x_532_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_533_;
v_res_533_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2____boxed(lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2167643761____hygCtx___hyg_2_();
return v_res_535_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_unsigned_to_nat(3035027224u);
v___x_542_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_543_ = l_Lean_Name_num___override(v___x_542_, v___x_541_);
return v___x_543_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_545_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_546_ = l_Lean_Name_str___override(v___x_545_, v___x_544_);
return v___x_546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_549_ = l_Lean_Name_str___override(v___x_548_, v___x_547_);
return v___x_549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_unsigned_to_nat(2u);
v___x_551_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_552_ = l_Lean_Name_num___override(v___x_551_, v___x_550_);
return v___x_552_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_554_; uint8_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_554_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_));
v___x_555_ = 1;
v___x_556_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_);
v___x_557_ = l_Lean_registerTraceClass(v___x_554_, v___x_555_, v___x_556_);
return v___x_557_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_558_;
v_res_558_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2____boxed(lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3035027224____hygCtx___hyg_2_();
return v_res_560_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_));
v___x_580_ = 1;
v___x_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_));
v___x_582_ = l_Lean_registerTraceClass(v___x_579_, v___x_580_, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_583_;
v_res_583_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
stack->m_obj
 = v_res_583_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2____boxed(lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1356401647____hygCtx___hyg_2_();
return v_res_585_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_));
v___x_604_ = 1;
v___x_605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_));
v___x_606_ = l_Lean_registerTraceClass(v___x_603_, v___x_604_, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_607_;
v_res_607_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
stack->m_obj
 = v_res_607_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2____boxed(lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_435833240____hygCtx___hyg_2_();
return v_res_609_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_617_ = lean_unsigned_to_nat(3832561742u);
v___x_618_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_619_ = l_Lean_Name_num___override(v___x_618_, v___x_617_);
return v___x_619_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_622_ = l_Lean_Name_str___override(v___x_621_, v___x_620_);
return v___x_622_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_624_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_625_ = l_Lean_Name_str___override(v___x_624_, v___x_623_);
return v___x_625_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_unsigned_to_nat(2u);
v___x_627_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_628_ = l_Lean_Name_num___override(v___x_627_, v___x_626_);
return v___x_628_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_));
v___x_631_ = 0;
v___x_632_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_);
v___x_633_ = l_Lean_registerTraceClass(v___x_630_, v___x_631_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_634_;
v_res_634_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_();
stack->m_obj
 = v_res_634_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2____boxed(lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3832561742____hygCtx___hyg_2_();
return v_res_636_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_unsigned_to_nat(4253340762u);
v___x_642_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_643_ = l_Lean_Name_num___override(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_645_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_646_ = l_Lean_Name_str___override(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_648_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_649_ = l_Lean_Name_str___override(v___x_648_, v___x_647_);
return v___x_649_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(2u);
v___x_651_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_652_ = l_Lean_Name_num___override(v___x_651_, v___x_650_);
return v___x_652_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_654_; uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_));
v___x_655_ = 0;
v___x_656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_);
v___x_657_ = l_Lean_registerTraceClass(v___x_654_, v___x_655_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_658_;
v_res_658_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2____boxed(lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4253340762____hygCtx___hyg_2_();
return v_res_660_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_unsigned_to_nat(3209233474u);
v___x_667_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_668_ = l_Lean_Name_num___override(v___x_667_, v___x_666_);
return v___x_668_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_670_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_671_ = l_Lean_Name_str___override(v___x_670_, v___x_669_);
return v___x_671_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_673_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_674_ = l_Lean_Name_str___override(v___x_673_, v___x_672_);
return v___x_674_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = lean_unsigned_to_nat(2u);
v___x_676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_677_ = l_Lean_Name_num___override(v___x_676_, v___x_675_);
return v___x_677_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_679_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_));
v___x_680_ = 0;
v___x_681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_);
v___x_682_ = l_Lean_registerTraceClass(v___x_679_, v___x_680_, v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_683_;
v_res_683_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
stack->m_obj
 = v_res_683_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2____boxed(lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3209233474____hygCtx___hyg_2_();
return v_res_685_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_691_ = lean_unsigned_to_nat(3765097528u);
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_693_ = l_Lean_Name_num___override(v___x_692_, v___x_691_);
return v___x_693_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_695_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_696_ = l_Lean_Name_str___override(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_699_ = l_Lean_Name_str___override(v___x_698_, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = lean_unsigned_to_nat(2u);
v___x_701_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_702_ = l_Lean_Name_num___override(v___x_701_, v___x_700_);
return v___x_702_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_));
v___x_705_ = 0;
v___x_706_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_);
v___x_707_ = l_Lean_registerTraceClass(v___x_704_, v___x_705_, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_708_;
v_res_708_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
stack->m_obj
 = v_res_708_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2____boxed(lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3765097528____hygCtx___hyg_2_();
return v_res_710_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_));
v___x_730_ = 0;
v___x_731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_));
v___x_732_ = l_Lean_registerTraceClass(v___x_729_, v___x_730_, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_733_;
v_res_733_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
stack->m_obj
 = v_res_733_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2____boxed(lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1713749687____hygCtx___hyg_2_();
return v_res_735_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_));
v___x_755_ = 0;
v___x_756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_));
v___x_757_ = l_Lean_registerTraceClass(v___x_754_, v___x_755_, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_758_;
v_res_758_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2____boxed(lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1374249216____hygCtx___hyg_2_();
return v_res_760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(2205948307u);
v___x_767_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_768_ = l_Lean_Name_num___override(v___x_767_, v___x_766_);
return v___x_768_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_771_ = l_Lean_Name_str___override(v___x_770_, v___x_769_);
return v___x_771_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_774_ = l_Lean_Name_str___override(v___x_773_, v___x_772_);
return v___x_774_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_775_ = lean_unsigned_to_nat(2u);
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_777_ = l_Lean_Name_num___override(v___x_776_, v___x_775_);
return v___x_777_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_779_; uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_));
v___x_780_ = 0;
v___x_781_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_);
v___x_782_ = l_Lean_registerTraceClass(v___x_779_, v___x_780_, v___x_781_);
return v___x_782_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_783_;
v_res_783_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
stack->m_obj
 = v_res_783_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2____boxed(lean_object* v_a_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2205948307____hygCtx___hyg_2_();
return v_res_785_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_791_ = lean_unsigned_to_nat(3880289020u);
v___x_792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_793_ = l_Lean_Name_num___override(v___x_792_, v___x_791_);
return v___x_793_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_794_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_796_ = l_Lean_Name_str___override(v___x_795_, v___x_794_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_798_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_799_ = l_Lean_Name_str___override(v___x_798_, v___x_797_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_800_ = lean_unsigned_to_nat(2u);
v___x_801_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_802_ = l_Lean_Name_num___override(v___x_801_, v___x_800_);
return v___x_802_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_));
v___x_805_ = 0;
v___x_806_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_);
v___x_807_ = l_Lean_registerTraceClass(v___x_804_, v___x_805_, v___x_806_);
return v___x_807_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_808_;
v_res_808_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2____boxed(lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3880289020____hygCtx___hyg_2_();
return v_res_810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = lean_unsigned_to_nat(3921417167u);
v___x_817_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_818_ = l_Lean_Name_num___override(v___x_817_, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_820_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_821_ = l_Lean_Name_str___override(v___x_820_, v___x_819_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_823_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_824_ = l_Lean_Name_str___override(v___x_823_, v___x_822_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(2u);
v___x_826_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_827_ = l_Lean_Name_num___override(v___x_826_, v___x_825_);
return v___x_827_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_829_; uint8_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_));
v___x_830_ = 0;
v___x_831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_);
v___x_832_ = l_Lean_registerTraceClass(v___x_829_, v___x_830_, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_833_;
v_res_833_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2____boxed(lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3921417167____hygCtx___hyg_2_();
return v_res_835_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_853_; uint8_t v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_));
v___x_854_ = 0;
v___x_855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_));
v___x_856_ = l_Lean_registerTraceClass(v___x_853_, v___x_854_, v___x_855_);
return v___x_856_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_857_;
v_res_857_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
stack->m_obj
 = v_res_857_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2____boxed(lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_328880924____hygCtx___hyg_2_();
return v_res_859_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_878_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_));
v___x_879_ = 0;
v___x_880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_));
v___x_881_ = l_Lean_registerTraceClass(v___x_878_, v___x_879_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_882_;
v_res_882_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
stack->m_obj
 = v_res_882_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2____boxed(lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1932954739____hygCtx___hyg_2_();
return v_res_884_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_));
v___x_906_ = 0;
v___x_907_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_));
v___x_908_ = l_Lean_registerTraceClass(v___x_905_, v___x_906_, v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_909_;
v_res_909_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
stack->m_obj
 = v_res_909_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2____boxed(lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_904368556____hygCtx___hyg_2_();
return v_res_911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_unsigned_to_nat(3036382584u);
v___x_918_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_919_ = l_Lean_Name_num___override(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_921_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_922_ = l_Lean_Name_str___override(v___x_921_, v___x_920_);
return v___x_922_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_924_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_925_ = l_Lean_Name_str___override(v___x_924_, v___x_923_);
return v___x_925_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_unsigned_to_nat(2u);
v___x_927_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_928_ = l_Lean_Name_num___override(v___x_927_, v___x_926_);
return v___x_928_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_930_; uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_930_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_));
v___x_931_ = 0;
v___x_932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_);
v___x_933_ = l_Lean_registerTraceClass(v___x_930_, v___x_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_934_;
v_res_934_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2____boxed(lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3036382584____hygCtx___hyg_2_();
return v_res_936_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_941_ = lean_unsigned_to_nat(3129348886u);
v___x_942_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_943_ = l_Lean_Name_num___override(v___x_942_, v___x_941_);
return v___x_943_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_945_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_946_ = l_Lean_Name_str___override(v___x_945_, v___x_944_);
return v___x_946_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_948_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_949_ = l_Lean_Name_str___override(v___x_948_, v___x_947_);
return v___x_949_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_unsigned_to_nat(2u);
v___x_951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_952_ = l_Lean_Name_num___override(v___x_951_, v___x_950_);
return v___x_952_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_954_; uint8_t v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_954_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_));
v___x_955_ = 0;
v___x_956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_);
v___x_957_ = l_Lean_registerTraceClass(v___x_954_, v___x_955_, v___x_956_);
return v___x_957_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_958_;
v_res_958_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
stack->m_obj
 = v_res_958_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2____boxed(lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3129348886____hygCtx___hyg_2_();
return v_res_960_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_unsigned_to_nat(4094675293u);
v___x_966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_967_ = l_Lean_Name_num___override(v___x_966_, v___x_965_);
return v___x_967_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_969_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_970_ = l_Lean_Name_str___override(v___x_969_, v___x_968_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_971_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_972_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_973_ = l_Lean_Name_str___override(v___x_972_, v___x_971_);
return v___x_973_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_974_ = lean_unsigned_to_nat(2u);
v___x_975_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_976_ = l_Lean_Name_num___override(v___x_975_, v___x_974_);
return v___x_976_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_978_; uint8_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_978_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_));
v___x_979_ = 0;
v___x_980_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_);
v___x_981_ = l_Lean_registerTraceClass(v___x_978_, v___x_979_, v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_982_;
v_res_982_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
stack->m_obj
 = v_res_982_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2____boxed(lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4094675293____hygCtx___hyg_2_();
return v_res_984_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_));
v___x_1004_ = 0;
v___x_1005_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_));
v___x_1006_ = l_Lean_registerTraceClass(v___x_1003_, v___x_1004_, v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1007_;
v_res_1007_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2____boxed(lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_1279589469____hygCtx___hyg_2_();
return v_res_1009_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_));
v___x_1030_ = 0;
v___x_1031_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_));
v___x_1032_ = l_Lean_registerTraceClass(v___x_1029_, v___x_1030_, v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1033_;
v_res_1033_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1033_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2____boxed(lean_object* v_a_1034_){
_start:
{
lean_object* v_res_1035_; 
v_res_1035_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_901832444____hygCtx___hyg_2_();
return v_res_1035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_unsigned_to_nat(2833612631u);
v___x_1043_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1044_ = l_Lean_Name_num___override(v___x_1043_, v___x_1042_);
return v___x_1044_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1046_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1047_ = l_Lean_Name_str___override(v___x_1046_, v___x_1045_);
return v___x_1047_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1049_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1050_ = l_Lean_Name_str___override(v___x_1049_, v___x_1048_);
return v___x_1050_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_unsigned_to_nat(2u);
v___x_1052_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1053_ = l_Lean_Name_num___override(v___x_1052_, v___x_1051_);
return v___x_1053_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_));
v___x_1056_ = 0;
v___x_1057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_);
v___x_1058_ = l_Lean_registerTraceClass(v___x_1055_, v___x_1056_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1059_;
v_res_1059_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1059_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2____boxed(lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2833612631____hygCtx___hyg_2_();
return v_res_1061_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1066_ = lean_unsigned_to_nat(3357376128u);
v___x_1067_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1068_ = l_Lean_Name_num___override(v___x_1067_, v___x_1066_);
return v___x_1068_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1070_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1071_ = l_Lean_Name_str___override(v___x_1070_, v___x_1069_);
return v___x_1071_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1072_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1073_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1074_ = l_Lean_Name_str___override(v___x_1073_, v___x_1072_);
return v___x_1074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_unsigned_to_nat(2u);
v___x_1076_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1077_ = l_Lean_Name_num___override(v___x_1076_, v___x_1075_);
return v___x_1077_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_));
v___x_1080_ = 0;
v___x_1081_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_);
v___x_1082_ = l_Lean_registerTraceClass(v___x_1079_, v___x_1080_, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1083_;
v_res_1083_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1083_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2____boxed(lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3357376128____hygCtx___hyg_2_();
return v_res_1085_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1103_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_));
v___x_1104_ = 0;
v___x_1105_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_));
v___x_1106_ = l_Lean_registerTraceClass(v___x_1103_, v___x_1104_, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1107_;
v_res_1107_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1107_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2____boxed(lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_942114620____hygCtx___hyg_2_();
return v_res_1109_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = lean_unsigned_to_nat(3746484445u);
v___x_1116_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1117_ = l_Lean_Name_num___override(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1120_ = l_Lean_Name_str___override(v___x_1119_, v___x_1118_);
return v___x_1120_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1122_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1123_ = l_Lean_Name_str___override(v___x_1122_, v___x_1121_);
return v___x_1123_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = lean_unsigned_to_nat(2u);
v___x_1125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1126_ = l_Lean_Name_num___override(v___x_1125_, v___x_1124_);
return v___x_1126_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1128_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_));
v___x_1129_ = 0;
v___x_1130_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_);
v___x_1131_ = l_Lean_registerTraceClass(v___x_1128_, v___x_1129_, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1132_;
v_res_1132_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2____boxed(lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3746484445____hygCtx___hyg_2_();
return v_res_1134_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_unsigned_to_nat(4104889296u);
v___x_1141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1142_ = l_Lean_Name_num___override(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1145_ = l_Lean_Name_str___override(v___x_1144_, v___x_1143_);
return v___x_1145_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1148_ = l_Lean_Name_str___override(v___x_1147_, v___x_1146_);
return v___x_1148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_unsigned_to_nat(2u);
v___x_1150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1151_ = l_Lean_Name_num___override(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_));
v___x_1154_ = 0;
v___x_1155_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_);
v___x_1156_ = l_Lean_registerTraceClass(v___x_1153_, v___x_1154_, v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1157_;
v_res_1157_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1157_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2____boxed(lean_object* v_a_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_4104889296____hygCtx___hyg_2_();
return v_res_1159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1165_ = lean_unsigned_to_nat(3575722790u);
v___x_1166_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1167_ = l_Lean_Name_num___override(v___x_1166_, v___x_1165_);
return v___x_1167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1170_ = l_Lean_Name_str___override(v___x_1169_, v___x_1168_);
return v___x_1170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1171_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1173_ = l_Lean_Name_str___override(v___x_1172_, v___x_1171_);
return v___x_1173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1174_ = lean_unsigned_to_nat(2u);
v___x_1175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1176_ = l_Lean_Name_num___override(v___x_1175_, v___x_1174_);
return v___x_1176_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_));
v___x_1179_ = 0;
v___x_1180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_);
v___x_1181_ = l_Lean_registerTraceClass(v___x_1178_, v___x_1179_, v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1182_;
v_res_1182_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1182_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2____boxed(lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_3575722790____hygCtx___hyg_2_();
return v_res_1184_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1202_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_));
v___x_1203_ = 0;
v___x_1204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_));
v___x_1205_ = l_Lean_registerTraceClass(v___x_1202_, v___x_1203_, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1206_;
v_res_1206_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1206_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2____boxed(lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_152317745____hygCtx___hyg_2_();
return v_res_1208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_unsigned_to_nat(2489964793u);
v___x_1215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1216_ = l_Lean_Name_num___override(v___x_1215_, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1219_ = l_Lean_Name_str___override(v___x_1218_, v___x_1217_);
return v___x_1219_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1221_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1222_ = l_Lean_Name_str___override(v___x_1221_, v___x_1220_);
return v___x_1222_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1223_ = lean_unsigned_to_nat(2u);
v___x_1224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1225_ = l_Lean_Name_num___override(v___x_1224_, v___x_1223_);
return v___x_1225_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1227_; uint8_t v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_));
v___x_1228_ = 0;
v___x_1229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_);
v___x_1230_ = l_Lean_registerTraceClass(v___x_1227_, v___x_1228_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1231_;
v_res_1231_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1231_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2____boxed(lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2489964793____hygCtx___hyg_2_();
return v_res_1233_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_unsigned_to_nat(2691769277u);
v___x_1240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1241_ = l_Lean_Name_num___override(v___x_1240_, v___x_1239_);
return v___x_1241_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1244_ = l_Lean_Name_str___override(v___x_1243_, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__25_00___x40_Lean_Meta_Tactic_Grind_1240498661____hygCtx___hyg_2_));
v___x_1246_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1247_ = l_Lean_Name_str___override(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_unsigned_to_nat(2u);
v___x_1249_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1250_ = l_Lean_Name_num___override(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_));
v___x_1253_ = 0;
v___x_1254_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_);
v___x_1255_ = l_Lean_registerTraceClass(v___x_1252_, v___x_1253_, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1256_;
v_res_1256_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1256_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2____boxed(lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_Tactic_Grind_0__Lean_initFn_00___x40_Lean_Meta_Tactic_Grind_2691769277____hygCtx___hyg_2_();
return v_res_1258_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagateChar(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BitVec(uint8_t builtin);
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
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_MarkAccessible(builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagateChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_BitVec(builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
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
res = runtime_initialize_Lean_Meta_Tactic_Grind_BVDecide(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkAccessible(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_MarkNestedSubsingletons(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Inv(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagateChar(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_BitVec(uint8_t builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Homomorphism(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Action(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheoremParam(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchAction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Filter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_CollectParams(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Finish(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_RegisterCommand(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_BVDecide(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MarkAccessible(builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_PropagateChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_BitVec(builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Homomorphism(builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_BVDecide(builtin);
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

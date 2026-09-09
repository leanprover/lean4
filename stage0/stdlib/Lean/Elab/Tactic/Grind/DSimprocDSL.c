// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.DSimprocDSL
// Imports: public import Lean.Elab.Tactic.Grind.Basic public import Lean.Meta.Sym.DSimp import Init.Sym.DSimp.DSimprocDSL
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "builtin_sym_dsimproc"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 195, 177, 54, 51, 15, 28, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "sym_dsimproc"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 104, 155, 90, 124, 179, 234, 41)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "DSimp"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 19, 66, 194, 48, 33, 24, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "SymDSimprocElab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(114, 142, 87, 230, 216, 59, 209, 149)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "symDSimprocElabAttribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 241, 189, 230, 45, 209, 62, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unsupported sym_dsimproc syntax `"};
static const lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_34_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_));
v___x_35_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_));
v___x_36_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_));
v___x_37_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_));
v___x_38_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_));
v___x_39_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_));
v___x_40_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_34_, v___x_36_, v___x_37_, v___x_38_, v___x_35_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2____boxed(lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_();
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2(lean_object* v_msgData_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___x_49_; lean_object* v_env_50_; lean_object* v___x_51_; lean_object* v_toCold_52_; lean_object* v_mctx_53_; lean_object* v_lctx_54_; lean_object* v_options_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_49_ = lean_st_ref_get(v___y_47_);
v_env_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_env_50_);
lean_dec(v___x_49_);
v___x_51_ = lean_st_ref_get(v___y_45_);
v_toCold_52_ = lean_ctor_get(v___y_46_, 0);
v_mctx_53_ = lean_ctor_get(v___x_51_, 0);
lean_inc_ref(v_mctx_53_);
lean_dec(v___x_51_);
v_lctx_54_ = lean_ctor_get(v___y_44_, 2);
v_options_55_ = lean_ctor_get(v_toCold_52_, 2);
lean_inc_ref(v_options_55_);
lean_inc_ref(v_lctx_54_);
v___x_56_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_56_, 0, v_env_50_);
lean_ctor_set(v___x_56_, 1, v_mctx_53_);
lean_ctor_set(v___x_56_, 2, v_lctx_54_);
lean_ctor_set(v___x_56_, 3, v_options_55_);
v___x_57_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v_msgData_43_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2(v_msgData_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_);
lean_dec(v___y_63_);
lean_dec_ref(v___y_62_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(lean_object* v_msg_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_ref_72_; lean_object* v___x_73_; lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_82_; 
v_ref_72_ = lean_ctor_get(v___y_69_, 2);
v___x_73_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1_spec__2(v_msg_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_82_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_82_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
lean_inc(v_ref_72_);
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v_ref_72_);
lean_ctor_set(v___x_78_, 1, v_a_74_);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 1);
lean_ctor_set(v___x_76_, 0, v___x_78_);
v___x_80_ = v___x_76_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg___boxed(lean_object* v_msg_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(v_msg_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_);
lean_dec(v___y_87_);
lean_dec_ref(v___y_86_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(lean_object* v_ref_90_, lean_object* v_msg_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_toCold_101_; lean_object* v_currRecDepth_102_; lean_object* v_ref_103_; uint8_t v_diag_104_; uint8_t v_suppressElabErrors_105_; lean_object* v_ref_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_toCold_101_ = lean_ctor_get(v___y_98_, 0);
v_currRecDepth_102_ = lean_ctor_get(v___y_98_, 1);
v_ref_103_ = lean_ctor_get(v___y_98_, 2);
v_diag_104_ = lean_ctor_get_uint8(v___y_98_, sizeof(void*)*3);
v_suppressElabErrors_105_ = lean_ctor_get_uint8(v___y_98_, sizeof(void*)*3 + 1);
v_ref_106_ = l_Lean_replaceRef(v_ref_90_, v_ref_103_);
lean_inc(v_currRecDepth_102_);
lean_inc_ref(v_toCold_101_);
v___x_107_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_107_, 0, v_toCold_101_);
lean_ctor_set(v___x_107_, 1, v_currRecDepth_102_);
lean_ctor_set(v___x_107_, 2, v_ref_106_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*3, v_diag_104_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*3 + 1, v_suppressElabErrors_105_);
v___x_108_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(v_msg_91_, v___y_96_, v___y_97_, v___x_107_, v___y_99_);
lean_dec_ref_known(v___x_107_, 3);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg___boxed(lean_object* v_ref_109_, lean_object* v_msg_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(v_ref_109_, v_msg_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v_ref_109_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(lean_object* v_stx_124_, lean_object* v_as_x27_125_, lean_object* v_b_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
if (lean_obj_tag(v_as_x27_125_) == 0)
{
lean_object* v___x_136_; 
lean_dec(v_stx_124_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v_b_126_);
return v___x_136_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v___x_139_; 
lean_dec_ref(v_b_126_);
v_head_137_ = lean_ctor_get(v_as_x27_125_, 0);
v_tail_138_ = lean_ctor_get(v_as_x27_125_, 1);
v___x_139_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_128_, v___y_130_, v___y_132_, v___y_134_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v_value_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref_known(v___x_139_, 1);
v_value_141_ = lean_ctor_get(v_head_137_, 1);
v___x_142_ = lean_box(0);
lean_inc(v_value_141_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
lean_inc(v___y_130_);
lean_inc_ref(v___y_129_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v_stx_124_);
v___x_143_ = lean_apply_10(v_value_141_, v_stx_124_, v___y_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
if (lean_obj_tag(v___x_143_) == 0)
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_a_140_);
lean_dec(v_stx_124_);
v_a_144_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_153_ == 0)
{
v___x_146_ = v___x_143_;
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_143_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_153_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v_a_144_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_142_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 0, v___x_149_);
v___x_151_ = v___x_146_;
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
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_190_; 
v_a_154_ = lean_ctor_get(v___x_143_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_190_ == 0)
{
v___x_156_ = v___x_143_;
v_isShared_157_ = v_isSharedCheck_190_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_143_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_190_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; uint8_t v___y_160_; uint8_t v___x_188_; 
v___x_158_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0));
v___x_188_ = l_Lean_Exception_isInterrupt(v_a_154_);
if (v___x_188_ == 0)
{
uint8_t v___x_189_; 
lean_inc(v_a_154_);
v___x_189_ = l_Lean_Exception_isRuntime(v_a_154_);
v___y_160_ = v___x_189_;
goto v___jp_159_;
}
else
{
v___y_160_ = v___x_188_;
goto v___jp_159_;
}
v___jp_159_:
{
if (v___y_160_ == 0)
{
lean_object* v___x_161_; 
lean_del_object(v___x_156_);
v___x_161_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_140_, v___y_160_, v___y_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_175_; 
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; 
v_unused_176_ = lean_ctor_get(v___x_161_, 0);
lean_dec(v_unused_176_);
v___x_163_ = v___x_161_;
v_isShared_164_ = v_isSharedCheck_175_;
goto v_resetjp_162_;
}
else
{
lean_dec(v___x_161_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_175_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
if (lean_obj_tag(v_a_154_) == 1)
{
lean_object* v_id_165_; lean_object* v___x_166_; uint8_t v___x_167_; 
v_id_165_ = lean_ctor_get(v_a_154_, 0);
v___x_166_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_167_ = l_Lean_instBEqInternalExceptionId_beq(v_id_165_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_169_; 
lean_dec(v_stx_124_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v_a_154_);
v___x_169_ = v___x_163_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_154_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
else
{
lean_dec_ref_known(v_a_154_, 2);
lean_del_object(v___x_163_);
v_as_x27_125_ = v_tail_138_;
v_b_126_ = v___x_158_;
goto _start;
}
}
else
{
lean_object* v___x_173_; 
lean_dec(v_stx_124_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v_a_154_);
v___x_173_ = v___x_163_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_154_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_a_154_);
lean_dec(v_stx_124_);
v_a_177_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_161_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_161_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
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
lean_object* v___x_186_; 
lean_dec(v_a_140_);
lean_dec(v_stx_124_);
if (v_isShared_157_ == 0)
{
v___x_186_ = v___x_156_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_154_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_stx_124_);
v_a_191_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_139_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_139_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___boxed(lean_object* v_stx_199_, lean_object* v_as_x27_200_, lean_object* v_b_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(v_stx_199_, v_as_x27_200_, v_b_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v_as_x27_200_);
return v_res_211_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__0));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__2));
v___x_217_ = l_Lean_stringToMessageData(v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc(lean_object* v_stx_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v___x_228_; lean_object* v_env_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_228_ = lean_st_ref_get(v_a_226_);
v_env_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_env_229_);
lean_dec(v___x_228_);
v___x_230_ = l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute;
lean_inc_n(v_stx_218_, 2);
v___x_231_ = l_Lean_Syntax_getKind(v_stx_218_);
v___x_232_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_230_, v_env_229_, v___x_231_);
v___x_233_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg___closed__0));
v___x_234_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(v_stx_218_, v___x_232_, v___x_233_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v___x_232_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_257_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_257_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_257_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_257_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_fst_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_255_; 
v_fst_239_ = lean_ctor_get(v_a_235_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v_a_235_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; 
v_unused_256_ = lean_ctor_get(v_a_235_, 1);
lean_dec(v_unused_256_);
v___x_241_ = v_a_235_;
v_isShared_242_ = v_isSharedCheck_255_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_fst_239_);
lean_dec(v_a_235_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_255_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
if (lean_obj_tag(v_fst_239_) == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
lean_del_object(v___x_237_);
v___x_243_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1, &l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1_once, _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__1);
v___x_244_ = l_Lean_MessageData_ofName(v___x_231_);
if (v_isShared_242_ == 0)
{
lean_ctor_set_tag(v___x_241_, 7);
lean_ctor_set(v___x_241_, 1, v___x_244_);
lean_ctor_set(v___x_241_, 0, v___x_243_);
v___x_246_ = v___x_241_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_243_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_250_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3, &l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3_once, _init_l_Lean_Elab_Tactic_Grind_elabSymDSimproc___closed__3);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(v_stx_218_, v___x_248_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_stx_218_);
return v___x_249_;
}
}
else
{
lean_object* v_val_251_; lean_object* v___x_253_; 
lean_del_object(v___x_241_);
lean_dec(v___x_231_);
lean_dec(v_stx_218_);
v_val_251_ = lean_ctor_get(v_fst_239_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v_fst_239_, 1);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v_val_251_);
v___x_253_ = v___x_237_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_val_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec(v___x_231_);
lean_dec(v_stx_218_);
v_a_258_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_234_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_234_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDSimproc___boxed(lean_object* v_stx_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_Tactic_Grind_elabSymDSimproc(v_stx_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec(v_a_268_);
lean_dec_ref(v_a_267_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0(lean_object* v_stx_277_, lean_object* v_as_278_, lean_object* v_as_x27_279_, lean_object* v_b_280_, lean_object* v_a_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___redArg(v_stx_277_, v_as_x27_279_, v_b_280_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0___boxed(lean_object* v_stx_292_, lean_object* v_as_293_, lean_object* v_as_x27_294_, lean_object* v_b_295_, lean_object* v_a_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__0(v_stx_292_, v_as_293_, v_as_x27_294_, v_b_295_, v_a_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v_as_x27_294_);
lean_dec(v_as_293_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1(lean_object* v_00_u03b1_307_, lean_object* v_ref_308_, lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___redArg(v_ref_308_, v_msg_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1___boxed(lean_object* v_00_u03b1_320_, lean_object* v_ref_321_, lean_object* v_msg_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1(v_00_u03b1_320_, v_ref_321_, v_msg_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v_ref_321_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1(lean_object* v_00_u03b1_333_, lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___redArg(v_msg_334_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1___boxed(lean_object* v_00_u03b1_345_, lean_object* v_msg_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymDSimproc_spec__1_spec__1(v_00_u03b1_345_, v_msg_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v___y_352_);
lean_dec_ref(v___y_351_);
lean_dec(v___y_350_);
lean_dec_ref(v___y_349_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_356_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_DSimp_DSimprocDSL(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_DSimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_DSimprocDSL_94594544____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Grind_symDSimprocElabAttribute);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
lean_object* initialize_Init_Sym_DSimp_DSimprocDSL(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_DSimp_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
}
#ifdef __cplusplus
}
#endif

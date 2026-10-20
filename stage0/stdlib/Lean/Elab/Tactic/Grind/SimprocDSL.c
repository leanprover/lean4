// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.SimprocDSL
// Imports: public import Lean.Elab.Tactic.Grind.Basic public import Lean.Meta.Sym.Simp.Discharger import Init.Sym.Simp.SimprocDSL
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_sym_simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 52, 107, 20, 11, 141, 213, 16)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "sym_simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 46, 43, 108, 212, 246, 33, 245)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sym"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 243, 118, 39, 175, 170, 127, 242)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 183, 106, 149, 74, 106, 130, 246)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "SymSimprocElab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 134, 251, 151, 217, 237, 141, 167)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "symSimprocElabAttribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 126, 35, 218, 239, 248, 28, 72)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "builtin_sym_discharger"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 199, 244, 124, 135, 247, 240, 73)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "sym_discharger"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 224, 81, 146, 130, 88, 184, 234)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SymDischargerElab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 24, 26, 1, 174, 184, 47, 235)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "symDischargerElabAttribute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 99, 164, 119, 227, 118, 220, 78)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(213, 237, 175, 121, 31, 106, 239, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "unsupported sym_simproc syntax `"};
static const lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unsupported sym_discharger syntax `"};
static const lean_object* l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDischarger(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDischarger___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_34_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_));
v___x_35_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_));
v___x_36_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_));
v___x_37_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_));
v___x_38_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_));
v___x_39_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_));
v___x_40_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_34_, v___x_36_, v___x_37_, v___x_38_, v___x_35_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2____boxed(lean_object* v_a_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_();
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_64_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_));
v___x_65_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_));
v___x_66_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_));
v___x_67_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_));
v___x_68_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_));
v___x_69_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_));
v___x_70_ = l_Lean_Elab_mkElabAttribute___redArg(v___x_64_, v___x_66_, v___x_67_, v___x_68_, v___x_65_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2____boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_();
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2(lean_object* v_msgData_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; lean_object* v_env_80_; uint8_t v___x_81_; lean_object* v_env_82_; lean_object* v___x_83_; lean_object* v_toCold_84_; lean_object* v_mctx_85_; lean_object* v_lctx_86_; lean_object* v_options_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_79_ = lean_st_ref_get(v___y_77_);
v_env_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc_ref(v_env_80_);
lean_dec(v___x_79_);
v___x_81_ = 0;
v_env_82_ = l_Lean_Environment_setRecordingDeps(v_env_80_, v___x_81_);
v___x_83_ = lean_st_ref_get(v___y_75_);
v_toCold_84_ = lean_ctor_get(v___y_76_, 0);
v_mctx_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_mctx_85_);
lean_dec(v___x_83_);
v_lctx_86_ = lean_ctor_get(v___y_74_, 2);
v_options_87_ = lean_ctor_get(v_toCold_84_, 2);
lean_inc_ref(v_options_87_);
lean_inc_ref(v_lctx_86_);
v___x_88_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_88_, 0, v_env_82_);
lean_ctor_set(v___x_88_, 1, v_mctx_85_);
lean_ctor_set(v___x_88_, 2, v_lctx_86_);
lean_ctor_set(v___x_88_, 3, v_options_87_);
v___x_89_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v_msgData_73_);
v___x_90_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2(v_msgData_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(lean_object* v_msg_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_ref_104_; lean_object* v___x_105_; lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_114_; 
v_ref_104_ = lean_ctor_get(v___y_101_, 2);
v___x_105_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1_spec__2(v_msg_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_114_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_114_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v___x_112_; 
lean_inc(v_ref_104_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v_ref_104_);
lean_ctor_set(v___x_110_, 1, v_a_106_);
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 1);
lean_ctor_set(v___x_108_, 0, v___x_110_);
v___x_112_ = v___x_108_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg___boxed(lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(lean_object* v_ref_122_, lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v_toCold_133_; lean_object* v_currRecDepth_134_; lean_object* v_ref_135_; uint16_t v_optionFlags_136_; uint8_t v_suppressElabErrors_137_; uint8_t v_isRecordingDeps_138_; lean_object* v_ref_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_toCold_133_ = lean_ctor_get(v___y_130_, 0);
v_currRecDepth_134_ = lean_ctor_get(v___y_130_, 1);
v_ref_135_ = lean_ctor_get(v___y_130_, 2);
v_optionFlags_136_ = lean_ctor_get_uint16(v___y_130_, sizeof(void*)*3);
v_suppressElabErrors_137_ = lean_ctor_get_uint8(v___y_130_, sizeof(void*)*3 + 2);
v_isRecordingDeps_138_ = lean_ctor_get_uint8(v___y_130_, sizeof(void*)*3 + 3);
v_ref_139_ = l_Lean_replaceRef(v_ref_122_, v_ref_135_);
lean_inc(v_currRecDepth_134_);
lean_inc_ref(v_toCold_133_);
v___x_140_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_140_, 0, v_toCold_133_);
lean_ctor_set(v___x_140_, 1, v_currRecDepth_134_);
lean_ctor_set(v___x_140_, 2, v_ref_139_);
lean_ctor_set_uint16(v___x_140_, sizeof(void*)*3, v_optionFlags_136_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*3 + 2, v_suppressElabErrors_137_);
lean_ctor_set_uint8(v___x_140_, sizeof(void*)*3 + 3, v_isRecordingDeps_138_);
v___x_141_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(v_msg_123_, v___y_128_, v___y_129_, v___x_140_, v___y_131_);
lean_dec_ref_known(v___x_140_, 3);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg___boxed(lean_object* v_ref_142_, lean_object* v_msg_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(v_ref_142_, v_msg_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v_ref_142_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(lean_object* v_stx_157_, lean_object* v_as_x27_158_, lean_object* v_b_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
if (lean_obj_tag(v_as_x27_158_) == 0)
{
lean_object* v___x_169_; 
lean_dec(v_stx_157_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v_b_159_);
return v___x_169_;
}
else
{
lean_object* v_head_170_; lean_object* v_tail_171_; lean_object* v_value_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_dec_ref(v_b_159_);
v_head_170_ = lean_ctor_get(v_as_x27_158_, 0);
v_tail_171_ = lean_ctor_get(v_as_x27_158_, 1);
v_value_172_ = lean_ctor_get(v_head_170_, 1);
v___x_173_ = lean_box(0);
v___x_174_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0));
v___x_175_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_161_, v___y_163_, v___y_165_, v___y_167_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v_a_176_; lean_object* v___x_177_; 
v_a_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_a_176_);
lean_dec_ref_known(v___x_175_, 1);
lean_inc(v_value_172_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
lean_inc(v___y_165_);
lean_inc_ref(v___y_164_);
lean_inc(v___y_163_);
lean_inc_ref(v___y_162_);
lean_inc(v___y_161_);
lean_inc_ref(v___y_160_);
lean_inc(v_stx_157_);
v___x_177_ = lean_apply_10(v_value_172_, v_stx_157_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, lean_box(0));
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_a_176_);
lean_dec(v_stx_157_);
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_187_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v_a_178_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v___x_173_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 0, v___x_183_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_224_; 
v_a_188_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_224_ == 0)
{
v___x_190_ = v___x_177_;
v_isShared_191_ = v_isSharedCheck_224_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_177_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_224_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
uint8_t v___x_192_; 
v___x_192_ = l_Lean_Exception_isInterrupt(v_a_188_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; 
lean_inc(v_a_188_);
v___x_193_ = l_Lean_Exception_isRuntime(v_a_188_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_del_object(v___x_190_);
v___x_194_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_176_, v___x_193_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_208_; 
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_208_ == 0)
{
lean_object* v_unused_209_; 
v_unused_209_ = lean_ctor_get(v___x_194_, 0);
lean_dec(v_unused_209_);
v___x_196_ = v___x_194_;
v_isShared_197_ = v_isSharedCheck_208_;
goto v_resetjp_195_;
}
else
{
lean_dec(v___x_194_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_208_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
if (lean_obj_tag(v_a_188_) == 1)
{
lean_object* v_id_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v_id_198_ = lean_ctor_get(v_a_188_, 0);
v___x_199_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_200_ = l_Lean_instBEqInternalExceptionId_beq(v_id_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_202_; 
lean_dec(v_stx_157_);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 1);
lean_ctor_set(v___x_196_, 0, v_a_188_);
v___x_202_ = v___x_196_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_188_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
else
{
lean_dec_ref_known(v_a_188_, 2);
lean_del_object(v___x_196_);
v_as_x27_158_ = v_tail_171_;
v_b_159_ = v___x_174_;
goto _start;
}
}
else
{
lean_object* v___x_206_; 
lean_dec(v_stx_157_);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 1);
lean_ctor_set(v___x_196_, 0, v_a_188_);
v___x_206_ = v___x_196_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_188_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_a_188_);
lean_dec(v_stx_157_);
v_a_210_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_194_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_194_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v___x_219_; 
lean_dec(v_a_176_);
lean_dec(v_stx_157_);
if (v_isShared_191_ == 0)
{
v___x_219_ = v___x_190_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_188_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
else
{
lean_object* v___x_222_; 
lean_dec(v_a_176_);
lean_dec(v_stx_157_);
if (v_isShared_191_ == 0)
{
v___x_222_ = v___x_190_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_188_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec(v_stx_157_);
v_a_225_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_175_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_175_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___boxed(lean_object* v_stx_233_, lean_object* v_as_x27_234_, lean_object* v_b_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(v_stx_233_, v_as_x27_234_, v_b_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v_as_x27_234_);
return v_res_245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__0));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__2));
v___x_251_ = l_Lean_stringToMessageData(v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc(lean_object* v_stx_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___x_262_; lean_object* v_env_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_262_ = lean_st_ref_get(v_a_260_);
v_env_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc_ref(v_env_263_);
lean_dec(v___x_262_);
v___x_264_ = l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute;
lean_inc_n(v_stx_252_, 2);
v___x_265_ = l_Lean_Syntax_getKind(v_stx_252_);
v___x_266_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_264_, v_env_263_, v___x_265_);
v___x_267_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg___closed__0));
v___x_268_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(v_stx_252_, v___x_266_, v___x_267_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v___x_266_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_291_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_291_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_291_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_291_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v_fst_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_289_; 
v_fst_273_ = lean_ctor_get(v_a_269_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v_a_269_);
if (v_isSharedCheck_289_ == 0)
{
lean_object* v_unused_290_; 
v_unused_290_ = lean_ctor_get(v_a_269_, 1);
lean_dec(v_unused_290_);
v___x_275_ = v_a_269_;
v_isShared_276_ = v_isSharedCheck_289_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_fst_273_);
lean_dec(v_a_269_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_289_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
if (lean_obj_tag(v_fst_273_) == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_280_; 
lean_del_object(v___x_271_);
v___x_277_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1, &l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1_once, _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__1);
v___x_278_ = l_Lean_MessageData_ofName(v___x_265_);
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 7);
lean_ctor_set(v___x_275_, 1, v___x_278_);
lean_ctor_set(v___x_275_, 0, v___x_277_);
v___x_280_ = v___x_275_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_277_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___x_278_);
v___x_280_ = v_reuseFailAlloc_284_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3, &l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3_once, _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3);
v___x_282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(v_stx_252_, v___x_282_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
lean_dec(v_stx_252_);
return v___x_283_;
}
}
else
{
lean_object* v_val_285_; lean_object* v___x_287_; 
lean_del_object(v___x_275_);
lean_dec(v___x_265_);
lean_dec(v_stx_252_);
v_val_285_ = lean_ctor_get(v_fst_273_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v_fst_273_, 1);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v_val_285_);
v___x_287_ = v___x_271_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_val_285_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
lean_dec(v___x_265_);
lean_dec(v_stx_252_);
v_a_292_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_268_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_268_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymSimproc___boxed(lean_object* v_stx_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_Tactic_Grind_elabSymSimproc(v_stx_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0(lean_object* v_stx_311_, lean_object* v_as_312_, lean_object* v_as_x27_313_, lean_object* v_b_314_, lean_object* v_a_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___redArg(v_stx_311_, v_as_x27_313_, v_b_314_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0___boxed(lean_object* v_stx_326_, lean_object* v_as_327_, lean_object* v_as_x27_328_, lean_object* v_b_329_, lean_object* v_a_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__0(v_stx_326_, v_as_327_, v_as_x27_328_, v_b_329_, v_a_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v_as_x27_328_);
lean_dec(v_as_327_);
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1(lean_object* v_00_u03b1_341_, lean_object* v_ref_342_, lean_object* v_msg_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(v_ref_342_, v_msg_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___boxed(lean_object* v_00_u03b1_354_, lean_object* v_ref_355_, lean_object* v_msg_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1(v_00_u03b1_354_, v_ref_355_, v_msg_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
lean_dec(v___y_358_);
lean_dec_ref(v___y_357_);
lean_dec(v_ref_355_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1(lean_object* v_00_u03b1_367_, lean_object* v_msg_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___redArg(v_msg_368_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1___boxed(lean_object* v_00_u03b1_379_, lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1_spec__1(v_00_u03b1_379_, v_msg_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___y_386_);
lean_dec_ref(v___y_385_);
lean_dec(v___y_384_);
lean_dec_ref(v___y_383_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(lean_object* v_stx_394_, lean_object* v_as_x27_395_, lean_object* v_b_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
if (lean_obj_tag(v_as_x27_395_) == 0)
{
lean_object* v___x_406_; 
lean_dec(v_stx_394_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v_b_396_);
return v___x_406_;
}
else
{
lean_object* v_head_407_; lean_object* v_tail_408_; lean_object* v_value_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec_ref(v_b_396_);
v_head_407_ = lean_ctor_get(v_as_x27_395_, 0);
v_tail_408_ = lean_ctor_get(v_as_x27_395_, 1);
v_value_409_ = lean_ctor_get(v_head_407_, 1);
v___x_410_ = lean_box(0);
v___x_411_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0));
v___x_412_ = l_Lean_Elab_Tactic_Grind_saveState___redArg(v___y_398_, v___y_400_, v___y_402_, v___y_404_);
if (lean_obj_tag(v___x_412_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_414_; 
v_a_413_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_a_413_);
lean_dec_ref_known(v___x_412_, 1);
lean_inc(v_value_409_);
lean_inc(v___y_404_);
lean_inc_ref(v___y_403_);
lean_inc(v___y_402_);
lean_inc_ref(v___y_401_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
lean_inc(v_stx_394_);
v___x_414_ = lean_apply_10(v_value_409_, v_stx_394_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, lean_box(0));
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_a_413_);
lean_dec(v_stx_394_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_424_ == 0)
{
v___x_417_ = v___x_414_;
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_424_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_422_; 
v___x_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_419_, 0, v_a_415_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_410_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_420_);
v___x_422_ = v___x_417_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v___x_420_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
else
{
lean_object* v_a_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_461_; 
v_a_425_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_461_ == 0)
{
v___x_427_ = v___x_414_;
v_isShared_428_ = v_isSharedCheck_461_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_a_425_);
lean_dec(v___x_414_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_461_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
uint8_t v___x_429_; 
v___x_429_ = l_Lean_Exception_isInterrupt(v_a_425_);
if (v___x_429_ == 0)
{
uint8_t v___x_430_; 
lean_inc(v_a_425_);
v___x_430_ = l_Lean_Exception_isRuntime(v_a_425_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_del_object(v___x_427_);
v___x_431_ = l_Lean_Elab_Tactic_Grind_SavedState_restore___redArg(v_a_413_, v___x_430_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_445_; 
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_431_, 0);
lean_dec(v_unused_446_);
v___x_433_ = v___x_431_;
v_isShared_434_ = v_isSharedCheck_445_;
goto v_resetjp_432_;
}
else
{
lean_dec(v___x_431_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_445_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
if (lean_obj_tag(v_a_425_) == 1)
{
lean_object* v_id_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_id_435_ = lean_ctor_get(v_a_425_, 0);
v___x_436_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_437_ = l_Lean_instBEqInternalExceptionId_beq(v_id_435_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_439_; 
lean_dec(v_stx_394_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 1);
lean_ctor_set(v___x_433_, 0, v_a_425_);
v___x_439_ = v___x_433_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_425_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
else
{
lean_dec_ref_known(v_a_425_, 2);
lean_del_object(v___x_433_);
v_as_x27_395_ = v_tail_408_;
v_b_396_ = v___x_411_;
goto _start;
}
}
else
{
lean_object* v___x_443_; 
lean_dec(v_stx_394_);
if (v_isShared_434_ == 0)
{
lean_ctor_set_tag(v___x_433_, 1);
lean_ctor_set(v___x_433_, 0, v_a_425_);
v___x_443_ = v___x_433_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_425_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_a_425_);
lean_dec(v_stx_394_);
v_a_447_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_431_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_431_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
else
{
lean_object* v___x_456_; 
lean_dec(v_a_413_);
lean_dec(v_stx_394_);
if (v_isShared_428_ == 0)
{
v___x_456_ = v___x_427_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v_a_425_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
}
else
{
lean_object* v___x_459_; 
lean_dec(v_a_413_);
lean_dec(v_stx_394_);
if (v_isShared_428_ == 0)
{
v___x_459_ = v___x_427_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_a_425_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
}
}
}
else
{
lean_object* v_a_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_469_; 
lean_dec(v_stx_394_);
v_a_462_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_469_ == 0)
{
v___x_464_ = v___x_412_;
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_a_462_);
lean_dec(v___x_412_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_469_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_467_; 
if (v_isShared_465_ == 0)
{
v___x_467_ = v___x_464_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_a_462_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___boxed(lean_object* v_stx_470_, lean_object* v_as_x27_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(v_stx_470_, v_as_x27_471_, v_b_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v_as_x27_471_);
return v_res_482_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = ((lean_object*)(l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__0));
v___x_485_ = l_Lean_stringToMessageData(v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDischarger(lean_object* v_stx_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___x_496_; lean_object* v_env_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_496_ = lean_st_ref_get(v_a_494_);
v_env_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc_ref(v_env_497_);
lean_dec(v___x_496_);
v___x_498_ = l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute;
lean_inc_n(v_stx_486_, 2);
v___x_499_ = l_Lean_Syntax_getKind(v_stx_486_);
v___x_500_ = l_Lean_KeyedDeclsAttribute_getEntries___redArg(v___x_498_, v_env_497_, v___x_499_);
v___x_501_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg___closed__0));
v___x_502_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(v_stx_486_, v___x_500_, v___x_501_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v___x_500_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_525_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_525_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_525_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_525_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v_fst_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_523_; 
v_fst_507_ = lean_ctor_get(v_a_503_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_523_ == 0)
{
lean_object* v_unused_524_; 
v_unused_524_ = lean_ctor_get(v_a_503_, 1);
lean_dec(v_unused_524_);
v___x_509_ = v_a_503_;
v_isShared_510_ = v_isSharedCheck_523_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_fst_507_);
lean_dec(v_a_503_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_523_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
if (lean_obj_tag(v_fst_507_) == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_514_; 
lean_del_object(v___x_505_);
v___x_511_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1, &l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1_once, _init_l_Lean_Elab_Tactic_Grind_elabSymDischarger___closed__1);
v___x_512_ = l_Lean_MessageData_ofName(v___x_499_);
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 7);
lean_ctor_set(v___x_509_, 1, v___x_512_);
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_514_ = v___x_509_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_512_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_obj_once(&l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3, &l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3_once, _init_l_Lean_Elab_Tactic_Grind_elabSymSimproc___closed__3);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Grind_elabSymSimproc_spec__1___redArg(v_stx_486_, v___x_516_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_stx_486_);
return v___x_517_;
}
}
else
{
lean_object* v_val_519_; lean_object* v___x_521_; 
lean_del_object(v___x_509_);
lean_dec(v___x_499_);
lean_dec(v_stx_486_);
v_val_519_ = lean_ctor_get(v_fst_507_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v_fst_507_, 1);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 0, v_val_519_);
v___x_521_ = v___x_505_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_val_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
else
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v___x_499_);
lean_dec(v_stx_486_);
v_a_526_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_533_ == 0)
{
v___x_528_ = v___x_502_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_502_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_526_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Grind_elabSymDischarger___boxed(lean_object* v_stx_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_Tactic_Grind_elabSymDischarger(v_stx_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0(lean_object* v_stx_545_, lean_object* v_as_546_, lean_object* v_as_x27_547_, lean_object* v_b_548_, lean_object* v_a_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___redArg(v_stx_545_, v_as_x27_547_, v_b_548_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0___boxed(lean_object* v_stx_560_, lean_object* v_as_561_, lean_object* v_as_x27_562_, lean_object* v_b_563_, lean_object* v_a_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_List_forIn_x27_loop___at___00Lean_Elab_Tactic_Grind_elabSymDischarger_spec__0(v_stx_560_, v_as_561_, v_as_x27_562_, v_b_563_, v_a_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v_as_x27_562_);
lean_dec(v_as_561_);
return v_res_574_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* runtime_initialize_Init_Sym_Simp_SimprocDSL(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Sym_Simp_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_3970955078____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Grind_symSimprocElabAttribute);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_SimprocDSL_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_SimprocDSL_2342394239____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_Grind_symDischargerElabAttribute);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin);
lean_object* initialize_Init_Sym_Simp_SimprocDSL(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_SimprocDSL(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Sym_Simp_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
}
#ifdef __cplusplus
}
#endif

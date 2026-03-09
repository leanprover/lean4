// Lean compiler output
// Module: Lean.Linter.UnusedVariables
// Imports: public import Lean.Elab.Command public import Lean.Linter.Util
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
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "unusedVariables"};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 68, 232, 214, 89, 54, 102, 248)}};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "enable the 'unused variables' linter"};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 37, 136, 247, 40, 33, 245, 169)}};
static const lean_object* l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_unusedVariables;
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "funArgs"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 68, 232, 214, 89, 54, 102, 248)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(161, 129, 102, 114, 183, 248, 63, 246)}};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "enable the 'unused variables' linter to mark unused function arguments"};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 37, 136, 247, 40, 33, 245, 169)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 239, 19, 85, 193, 234, 14, 245)}};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_unusedVariables_funArgs;
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "patternVars"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 68, 232, 214, 89, 54, 102, 248)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(141, 144, 77, 59, 145, 126, 239, 241)}};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "enable the 'unused variables' linter to mark unused pattern variables"};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 37, 136, 247, 40, 33, 245, 169)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 104, 17, 140, 100, 188, 192, 98)}};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_unusedVariables_patternVars;
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "analyzeTactics"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(148, 68, 232, 214, 89, 54, 102, 248)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 229, 161, 52, 240, 110, 102, 128)}};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 473, .m_capacity = 473, .m_length = 472, .m_data = "enable analysis of local variables in presence of tactic proofs\n\nBy default, the linter will limit itself to linting a declaration's parameters whenever tactic proofs are present as these can be expensive to analyze. Enabling this option extends linting to local variables both inside and outside tactic proofs, though it can also lead to some false negatives as intermediate tactic states may reference some variables without the declaration ultimately depending on them."};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(39, 37, 136, 247, 40, 33, 245, 169)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(252, 28, 122, 212, 224, 62, 217, 150)}};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_unusedVariables_analyzeTactics;
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterUnusedVariables(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterUnusedVariables___boxed(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterUnusedVariablesFunArgs_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterUnusedVariablesFunArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterUnusedVariablesFunArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterUnusedVariablesFunArgs___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterUnusedVariablesPatternVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterUnusedVariablesPatternVars___boxed(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_mkIgnoreFnImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_Linter_mkIgnoreFnImpl___closed__0 = (const lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__0_value;
static const lean_string_object l_Lean_Linter_mkIgnoreFnImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Linter_mkIgnoreFnImpl___closed__1 = (const lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__1_value;
static const lean_string_object l_Lean_Linter_mkIgnoreFnImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "IgnoreFunction"};
static const lean_object* l_Lean_Linter_mkIgnoreFnImpl___closed__2 = (const lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__2_value;
static const lean_ctor_object l_Lean_Linter_mkIgnoreFnImpl___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_mkIgnoreFnImpl___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__3_value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_mkIgnoreFnImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__3_value_aux_1),((lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(6, 152, 72, 12, 151, 101, 181, 136)}};
static const lean_object* l_Lean_Linter_mkIgnoreFnImpl___closed__3 = (const lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__3_value;
static const lean_string_object l_Lean_Linter_mkIgnoreFnImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "unexpected unused_variables_ignore_fn at '"};
static const lean_object* l_Lean_Linter_mkIgnoreFnImpl___closed__4 = (const lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__4_value;
static const lean_string_object l_Lean_Linter_mkIgnoreFnImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "', must be of type `Lean.Linter.IgnoreFunction`"};
static const lean_object* l_Lean_Linter_mkIgnoreFnImpl___closed__5 = (const lean_object*)&l_Lean_Linter_mkIgnoreFnImpl___closed__5_value;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_mkIgnoreFnImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_mkIgnoreFnImpl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2__value;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_builtinUnusedVariablesIgnoreFnsRef;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn___boxed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object*);
static const lean_string_object l_Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "number of local entries: "};
static const lean_object* l_Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unusedVariablesIgnoreFnsExt"};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(196, 161, 171, 239, 245, 206, 14, 84)}};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_;
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_unusedVariablesIgnoreFnsExt;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Invalid attribute scope: Attribute `["};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "]` must be global, not `"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "global"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__5 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__5_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "local"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__6_value;
static const lean_string_object l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "scoped"};
static const lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__7 = (const lean_object*)&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__7_value;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "]`: Declaration `"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "` has type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__5;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "\nbut `["};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__6 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__6_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__7;
static const lean_string_object l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "]` can only be added to declarations of type"};
static const lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__8 = (const lean_object*)&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__8_value;
static lean_once_cell_t l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__9;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "addBuiltinUnusedVariablesIgnoreFn"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "UnusedVariables"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 209, 232, 248, 35, 241, 6, 59)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__5_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(46, 13, 252, 7, 151, 1, 58, 192)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__6_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(87, 230, 206, 172, 237, 181, 181, 27)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__7_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(173, 208, 164, 190, 31, 102, 180, 11)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__8_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__9_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 252, 165, 244, 62, 51, 136, 247)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__10_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__11_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 40, 91, 51, 145, 5, 157, 43)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__12_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(120, 120, 40, 188, 46, 167, 240, 12)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__13_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(78, 143, 189, 232, 224, 168, 61, 170)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__14_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 26, 213, 156, 161, 236, 49, 95)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__15_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1088826556) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(66, 102, 69, 71, 248, 185, 220, 9)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__16_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__17_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 217, 213, 110, 79, 254, 241, 154)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__18_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__19_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 4, 129, 131, 89, 244, 252, 234)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__20_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(128, 190, 167, 215, 169, 244, 245, 154)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "Marks a function of type `Lean.Linter.IgnoreFunction` for suppressing unused variable warnings"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "(builtin) "};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "builtin_unused_variables_ignore_fn"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 197, 125, 148, 30, 72, 0, 178)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unused_variables_ignore_fn"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(27, 15, 129, 252, 161, 118, 202, 200)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "variable"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 93, 226, 106, 76, 14, 69, 165)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
uint8_t l_Lean_Syntax_Stack_matches(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2____boxed(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "structure"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(180, 236, 187, 15, 83, 171, 117, 65)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inductive"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(167, 178, 72, 69, 244, 64, 6, 60)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__13_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__13_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__13_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "ctor"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 61, 118, 113, 180, 158, 239, 32)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "structSimpleBinder"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 230, 214, 182, 254, 52, 213, 225)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "opaque"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(111, 217, 152, 21, 13, 97, 204, 102)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "axiom"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__9_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(98, 213, 89, 132, 71, 178, 86, 86)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__10_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__8_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__11_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4_value;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "extern"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(174, 126, 252, 124, 35, 62, 180, 112)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implemented_by"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(221, 249, 143, 128, 101, 138, 146, 72)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__6_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1(uint8_t, lean_object*, size_t, size_t);
uint8_t l_Lean_Syntax_matchesIdent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "noncomputable"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "protected"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__9_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__10_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__12_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__12_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__12_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__13_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__12_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__13_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__13_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__14_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__13_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__14_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__14_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__15_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__14_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__15_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__15_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
uint8_t l_Lean_Syntax_isNone(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "depArrow"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(115, 137, 180, 163, 158, 211, 191, 168)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letIdDecl"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(82, 96, 243, 36, 251, 209, 136, 237)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "structInstField"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 77, 20, 88, 28, 210, 230, 84)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2____boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__3_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "typeAscription"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__5_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(247, 209, 88, 141, 5, 195, 49, 74)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__7_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inductionAltLHS"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(58, 206, 3, 35, 121, 94, 13, 140)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_once_cell_t l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__0;
static lean_once_cell_t l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__1;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg(size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___redArg(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0(lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1___redArg(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitEntry(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_visitAssignments_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_visitAssignments_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_UnusedVariables_visitAssignments___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_UnusedVariables_visitAssignments___closed__0;
static lean_once_cell_t l_Lean_Linter_UnusedVariables_visitAssignments___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_UnusedVariables_visitAssignments___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_visitAssignments(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_visitAssignments___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_followAliases(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_followAliases___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__0 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_findInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3_spec__6(uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__2;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11_spec__18___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__0_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3;
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__2_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__3;
extern lean_object* l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_4118479936____hygCtx___hyg_9_;
lean_object* l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
lean_object* l_Lean_Elab_Info_stx(lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11_spec__18(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_collectReferences(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_collectReferences___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sorry"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 85, 70, 0, 206, 11, 146, 59)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticSorry"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(254, 186, 126, 140, 105, 148, 113, 102)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticAdmit"};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(124, 238, 151, 162, 2, 58, 5, 140)}};
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___closed__0 = (const lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___closed__0_value;
lean_object* l_Lean_Syntax_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__2(lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__9(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__0_value;
static const lean_array_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__1_value;
uint8_t l_Lean_Elab_Info_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__0_value;
lean_object* l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Command_instMonadCommandElabM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__1_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___closed__0 = (const lean_object*)&l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10_spec__14(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8_spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__23(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__19(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0___closed__0_value;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__1;
static const lean_string_object l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unused variable `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0;
static lean_once_cell_t l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1;
static const lean_array_object l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__2 = (const lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__3;
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_UnusedVariables_unusedVariables___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___closed__0 = (const lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__0_value;
static const lean_ctor_object l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__4_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 107, 179, 72, 26, 88, 42, 169)}};
static const lean_ctor_object l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(125, 15, 230, 120, 165, 180, 64, 116)}};
static const lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___closed__1 = (const lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value;
static const lean_ctor_object l_Lean_Linter_UnusedVariables_unusedVariables___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__0_value),((lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__1_value)}};
static const lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___closed__2 = (const lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_UnusedVariables_unusedVariables = (const lean_object*)&l_Lean_Linter_UnusedVariables_unusedVariables___closed__2_value;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addLinter(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_initFn_00___x40_Lean_Linter_UnusedVariables_1044370963____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_initFn_00___x40_Lean_Linter_UnusedVariables_1044370963____hygCtx___hyg_2____boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_isUnusedVariableWarning___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isUnusedVariableWarning___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_MessageData_isUnusedVariableWarning___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_isUnusedVariableWarning___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_isUnusedVariableWarning___closed__0 = (const lean_object*)&l_Lean_MessageData_isUnusedVariableWarning___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_MessageData_isUnusedVariableWarning(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isUnusedVariableWarning___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_33; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
x_7 = x_2;
x_8 = x_33;
goto block_32;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_ctor(1, 0, 1);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_9, 0, x_10);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_6);
lean_inc(x_1);
x_12 = lean_register_option(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_22; 
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_13 = x_12;
x_14 = x_22;
goto block_21;
}
else
{
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_15; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 0, x_1);
x_15 = x_7;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_5);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 0, x_15);
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_del_object(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_24 = lean_ctor_get(x_12, 0);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
x_25 = x_12;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterUnusedVariables(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Linter_linter_unusedVariables;
x_3 = l_Lean_Linter_getLinterValue(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterUnusedVariables___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_getLinterUnusedVariables(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterUnusedVariablesFunArgs_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterUnusedVariablesFunArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterUnusedVariablesFunArgs_spec__0(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterUnusedVariablesFunArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = l_Lean_Linter_linter_unusedVariables_funArgs;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Linter_getLinterUnusedVariables(x_1);
x_5 = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterUnusedVariablesFunArgs_spec__0(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterUnusedVariablesFunArgs___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_getLinterUnusedVariablesFunArgs(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterUnusedVariablesPatternVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = l_Lean_Linter_linter_unusedVariables_patternVars;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Linter_getLinterUnusedVariables(x_1);
x_5 = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterUnusedVariablesFunArgs_spec__0(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterUnusedVariablesPatternVars___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Linter_getLinterUnusedVariablesPatternVars(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
x_4 = x_1;
x_5 = x_11;
goto block_10;
}
else
{
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = x_11;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_mk_io_user_error(x_3);
if (x_5 == 0)
{
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_6);
x_7 = x_4;
goto block_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_7 = x_9;
goto block_8;
}
block_8:
{
return x_7;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
x_13 = x_1;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 0);
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkIgnoreFnImpl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_2);
x_6 = 0;
lean_inc(x_1);
lean_inc_ref(x_4);
x_7 = l_Lean_Environment_find_x3f(x_4, x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_8 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__0));
x_9 = 1;
x_10 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_9);
x_11 = lean_string_append(x_8, x_10);
lean_dec_ref(x_10);
x_12 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = lean_mk_io_user_error(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_35; 
x_16 = lean_ctor_get(x_7, 0);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
x_17 = x_7;
x_18 = x_35;
goto block_34;
}
else
{
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_ConstantInfo_type(x_16);
lean_dec(x_16);
x_20 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__3));
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
lean_dec_ref(x_19);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_22 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__4));
x_23 = 1;
x_24 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec_ref(x_24);
x_26 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__5));
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_mk_io_user_error(x_27);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_28);
x_29 = x_17;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_del_object(x_17);
x_32 = l_Lean_Environment_evalConst___redArg(x_4, x_5, x_1, x_21);
lean_dec_ref(x_5);
x_33 = l_IO_ofExcept___at___00Lean_Linter_mkIgnoreFnImpl_spec__0___redArg(x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_mkIgnoreFnImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Linter_mkIgnoreFnImpl(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2_));
x_3 = lean_st_mk_ref(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Linter_builtinUnusedVariablesIgnoreFnsRef;
x_4 = lean_st_ref_take(x_3);
x_5 = lean_array_push(x_4, x_1);
x_6 = lean_st_ref_set(x_3, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = l_List_reverse___redArg(x_2);
x_4 = lean_array_mk(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_3 = x_1;
x_4 = x_13;
goto block_12;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_13;
goto block_12;
}
block_12:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = ((lean_object*)(l_Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_));
x_6 = l_List_lengthTR___redArg(x_2);
lean_dec(x_2);
x_7 = l_Nat_reprFast(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
if (x_4 == 0)
{
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_8);
lean_ctor_set(x_3, 0, x_5);
x_9 = x_3;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = l_List_reverse___redArg(x_4);
x_6 = lean_array_mk(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(x_1, x_2, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_21; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
x_5 = x_1;
x_6 = x_21;
goto block_20;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_19; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
x_9 = x_2;
x_10 = x_19;
goto block_18;
}
else
{
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_11; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 0, x_7);
x_11 = x_5;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_3);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_push(x_4, x_8);
if (x_10 == 0)
{
lean_ctor_set(x_9, 1, x_12);
lean_ctor_set(x_9, 0, x_11);
x_13 = x_9;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget_borrowed(x_1, x_2);
lean_inc_ref(x_5);
lean_inc(x_8);
x_9 = l_Lean_Linter_mkIgnoreFnImpl(x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_array_push(x_4, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_22; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_15 = lean_ctor_get(x_9, 0);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
x_16 = x_9;
x_17 = x_22;
goto block_21;
}
else
{
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_15);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
}
else
{
lean_object* x_23; 
lean_dec_ref(x_5);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_4);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_12; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_2, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_array_uget_borrowed(x_1, x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
x_7 = x_4;
goto block_11;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
if (x_19 == 0)
{
x_7 = x_4;
goto block_11;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_18);
lean_inc_ref(x_5);
x_23 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__0(x_16, x_21, x_22, x_4, x_5);
x_12 = x_23;
goto block_14;
}
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_18);
lean_inc_ref(x_5);
x_26 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__0(x_16, x_24, x_25, x_4, x_5);
x_12 = x_26;
goto block_14;
}
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_5);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_4);
return x_27;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
block_14:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_7 = x_13;
goto block_11;
}
else
{
lean_dec_ref(x_5);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__1(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_10; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_st_ref_get(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_2);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_dec_ref(x_3);
x_5 = x_21;
goto block_9;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_23, x_23);
if (x_25 == 0)
{
if (x_24 == 0)
{
lean_dec_ref(x_3);
x_5 = x_21;
goto block_9;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_23);
x_28 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__1(x_2, x_26, x_27, x_21, x_3);
x_10 = x_28;
goto block_20;
}
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_23);
x_31 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__spec__1(x_2, x_29, x_30, x_21, x_3);
x_10 = x_31;
goto block_20;
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_20:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_5 = x_11;
goto block_9;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_13 = x_10;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_builtinUnusedVariablesIgnoreFnsRef;
x_2 = lean_alloc_closure((void*)(l_Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Linter_builtinUnusedVariablesIgnoreFnsRef;
x_2 = lean_alloc_closure((void*)(l_Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(2);
x_3 = ((lean_object*)(l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_));
x_4 = ((lean_object*)(l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_));
x_5 = ((lean_object*)(l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_));
x_6 = lean_obj_once(&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_, &l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once, _init_l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_);
x_7 = lean_obj_once(&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_, &l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once, _init_l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_);
x_8 = ((lean_object*)(l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_));
x_9 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_3);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set(x_9, 7, x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_));
x_2 = lean_obj_once(&l_Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_, &l_Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once, _init_l_Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_, &l_Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2__once, _init_l_Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_);
x_3 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__0, &l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__0_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__1, &l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__1_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_22; 
x_4 = lean_st_ref_take(x_2);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_ctor_get(x_4, 4);
x_9 = lean_ctor_get(x_4, 6);
x_10 = lean_ctor_get(x_4, 7);
x_11 = lean_ctor_get(x_4, 8);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_4, 5);
lean_dec(x_23);
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_12 = x_4;
x_13 = x_22;
goto block_21;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_obj_once(&l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__2, &l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__2_once, _init_l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___closed__2);
if (x_13 == 0)
{
lean_ctor_set(x_12, 5, x_14);
lean_ctor_set(x_12, 0, x_1);
x_15 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_6);
lean_ctor_set(x_20, 3, x_7);
lean_ctor_set(x_20, 4, x_8);
lean_ctor_set(x_20, 5, x_14);
lean_ctor_set(x_20, 6, x_9);
lean_ctor_set(x_20, 7, x_10);
lean_ctor_set(x_20, 8, x_11);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_set(x_2, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__4(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__3);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__4);
x_3 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2);
x_9 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_15; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0(x_1, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
x_8 = x_6;
x_9 = x_15;
goto block_14;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_obj_once(&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_, &l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_);
x_7 = l_Lean_MessageData_ofName(x_1);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_obj_once(&l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_, &l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(x_10, x_3, x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__1);
x_7 = l_Lean_MessageData_ofName(x_1);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__3);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
switch (x_2) {
case 0:
{
lean_object* x_19; 
x_19 = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__5));
x_11 = x_19;
goto block_18;
}
case 1:
{
lean_object* x_20; 
x_20 = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__6));
x_11 = x_20;
goto block_18;
}
default: 
{
lean_object* x_21; 
x_21 = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__7));
x_11 = x_21;
goto block_18;
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_MessageData_ofFormat(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(x_16, x_3, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
x_7 = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg(x_1, x_6, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_30; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_ctor_get(x_3, 3);
x_10 = lean_ctor_get(x_3, 4);
x_11 = lean_ctor_get(x_3, 5);
x_12 = lean_ctor_get(x_3, 6);
x_13 = lean_ctor_get(x_3, 7);
x_14 = lean_ctor_get(x_3, 8);
x_15 = lean_ctor_get(x_3, 9);
x_16 = lean_ctor_get(x_3, 10);
x_17 = lean_ctor_get(x_3, 11);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*14);
x_19 = lean_ctor_get(x_3, 12);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*14 + 1);
x_21 = lean_ctor_get(x_3, 13);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
x_22 = x_3;
x_23 = x_30;
goto block_29;
}
else
{
lean_inc(x_21);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
if (x_23 == 0)
{
lean_ctor_set(x_22, 5, x_24);
x_25 = x_22;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_7);
lean_ctor_set(x_28, 2, x_8);
lean_ctor_set(x_28, 3, x_9);
lean_ctor_set(x_28, 4, x_10);
lean_ctor_set(x_28, 5, x_24);
lean_ctor_set(x_28, 6, x_12);
lean_ctor_set(x_28, 7, x_13);
lean_ctor_set(x_28, 8, x_14);
lean_ctor_set(x_28, 9, x_15);
lean_ctor_set(x_28, 10, x_16);
lean_ctor_set(x_28, 11, x_17);
lean_ctor_set(x_28, 12, x_19);
lean_ctor_set(x_28, 13, x_21);
lean_ctor_set_uint8(x_28, sizeof(void*)*14, x_18);
lean_ctor_set_uint8(x_28, sizeof(void*)*14 + 1, x_20);
x_25 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_26; 
x_26 = l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(x_2, x_25, x_4);
lean_dec_ref(x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2);
x_14 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5);
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_62; 
x_27 = lean_ctor_get(x_19, 0);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
x_28 = x_19;
x_29 = x_62;
goto block_61;
}
else
{
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_box(0);
x_31 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_32 = l_Lean_EnvironmentHeader_moduleNames(x_31);
x_33 = lean_array_get(x_30, x_32, x_27);
lean_dec(x_27);
lean_dec_ref(x_32);
x_34 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofName(x_33);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_note(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_44);
x_45 = x_28;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
x_50 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofName(x_33);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MessageData_note(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_57);
x_58 = x_28;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_16; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(x_1, x_2, x_4);
x_7 = lean_ctor_get(x_6, 0);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
x_8 = x_6;
x_9 = x_16;
goto block_15;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_unknownIdentifierMessageTag;
x_11 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8(x_2, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(x_1, x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___closed__0);
x_7 = 0;
lean_inc(x_2);
x_8 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(x_1, x_11, x_2, x_3, x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 5);
lean_inc(x_5);
x_6 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(x_5, x_1, x_2, x_3);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = 0;
lean_inc(x_1);
x_8 = l_Lean_Environment_find_x3f(x_6, x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___redArg(x_1, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
x_11 = x_8;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 0);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_8 = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__1);
x_9 = l_Lean_MessageData_ofName(x_1);
lean_inc_ref(x_9);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__3);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = l_Lean_MessageData_ofConstName(x_2, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__5);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_indentExpr(x_3);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__7);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_9);
x_23 = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__9, &l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__9_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___closed__9);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_indentExpr(x_4);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(x_26, x_5, x_6);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_49; lean_object* x_50; lean_object* x_69; lean_object* x_70; lean_object* x_75; 
lean_inc_ref(x_9);
x_75 = l_Lean_Attribute_Builtin_ensureNoArgs(x_7, x_9, x_10);
if (lean_obj_tag(x_75) == 0)
{
lean_dec_ref(x_75);
if (x_1 == 0)
{
lean_object* x_76; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_76 = l_Lean_ensureAttrDeclIsMeta(x_5, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_76);
x_69 = x_9;
x_70 = x_10;
goto block_74;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_76;
}
}
else
{
x_69 = x_9;
x_70 = x_10;
goto block_74;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_75;
}
block_48:
{
lean_object* x_14; 
x_14 = lean_st_ref_get(x_13);
if (x_1 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_15 = lean_st_ref_get(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_12, 5);
lean_inc(x_18);
lean_dec_ref(x_12);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_inc(x_6);
x_20 = l_Lean_Linter_mkIgnoreFnImpl(x_6, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_22);
lean_dec(x_14);
x_23 = l_Lean_Linter_unusedVariablesIgnoreFnsExt;
x_24 = lean_ctor_get(x_23, 0);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_21);
x_27 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_23, x_22, x_26, x_25, x_2);
lean_dec(x_25);
x_28 = l_Lean_setEnv___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__1___redArg(x_27, x_13);
lean_dec(x_13);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_2);
x_29 = lean_ctor_get(x_20, 0);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
x_30 = x_20;
x_31 = x_40;
goto block_39;
}
else
{
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_io_error_to_string(x_29);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_34);
if (x_31 == 0)
{
lean_ctor_set(x_30, 0, x_35);
x_36 = x_30;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_14);
lean_dec(x_2);
x_41 = lean_box(0);
lean_inc(x_6);
x_42 = l_Lean_mkConst(x_6, x_41);
x_43 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_44 = l_Lean_Name_mkStr3(x_3, x_4, x_43);
x_45 = l_Lean_mkConst(x_44, x_41);
x_46 = l_Lean_Expr_app___override(x_45, x_42);
x_47 = l_Lean_declareBuiltin(x_6, x_46, x_12, x_13);
return x_47;
}
}
block_68:
{
lean_object* x_51; 
lean_inc_ref(x_49);
lean_inc(x_6);
x_51 = l_Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2(x_6, x_49, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = l_Lean_ConstantInfo_type(x_52);
lean_dec(x_52);
x_54 = ((lean_object*)(l_Lean_Linter_mkIgnoreFnImpl___closed__2));
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_55 = l_Lean_Name_mkStr3(x_3, x_4, x_54);
x_56 = l_Lean_Expr_isConstOf(x_53, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = l_Lean_mkConst(x_55, x_57);
x_59 = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg(x_5, x_6, x_53, x_58, x_49, x_50);
lean_dec(x_50);
lean_dec_ref(x_49);
return x_59;
}
else
{
lean_dec(x_55);
lean_dec_ref(x_53);
lean_dec(x_5);
x_12 = x_49;
x_13 = x_50;
goto block_48;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_50);
lean_dec_ref(x_49);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_60 = lean_ctor_get(x_51, 0);
x_67 = !lean_is_exclusive(x_51);
if (x_67 == 0)
{
x_61 = x_51;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_51);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
block_74:
{
uint8_t x_71; uint8_t x_72; 
x_71 = 0;
x_72 = l_Lean_instBEqAttributeKind_beq(x_8, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_73 = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg(x_5, x_8, x_69, x_70);
lean_dec(x_70);
lean_dec_ref(x_69);
return x_73;
}
else
{
x_49 = x_69;
x_50 = x_70;
goto block_68;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_8);
x_14 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_box(0);
x_6 = ((lean_object*)(l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_));
x_7 = ((lean_object*)(l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_));
x_8 = lean_box(x_1);
lean_inc(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed), 11, 5);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_6);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_2);
x_10 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__21_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
if (x_1 == 0)
{
lean_object* x_19; 
x_19 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_11 = x_19;
goto block_18;
}
else
{
lean_object* x_20; 
x_20 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__24_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_11 = x_20;
goto block_18;
}
block_18:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__22_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_13 = lean_string_append(x_11, x_12);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*3, x_14);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_4);
x_17 = l_Lean_registerBuiltinAttribute(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_() {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
x_5 = 0;
x_6 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
x_7 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_(x_5, x_6);
return x_7;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwAttrDeclNotOfExpectedType___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
x_8 = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4(x_1, x_2, x_7, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___redArg(x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__2_spec__3_spec__4_spec__7_spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__11_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_));
x_5 = l_Lean_Syntax_Stack_matches(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_));
lean_inc(x_2);
x_5 = l_Lean_Syntax_Stack_matches(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(4u);
x_7 = l_List_get_x3fInternal___redArg(x_2, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__13_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_));
x_13 = l_List_any___redArg(x_12, x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__7_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_));
lean_inc(x_2);
x_5 = l_Lean_Syntax_Stack_matches(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(4u);
x_7 = l_List_get_x3fInternal___redArg(x_2, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__5_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_));
x_13 = l_List_any___redArg(x_12, x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__6_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_));
lean_inc(x_2);
x_5 = l_Lean_Syntax_Stack_matches(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(4u);
x_7 = l_List_get_x3fInternal___redArg(x_2, x_6);
lean_dec(x_2);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__12_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_));
x_13 = l_List_any___redArg(x_12, x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__2));
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_6, x_10);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__4));
lean_inc(x_11);
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec_ref(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Syntax_getArg(x_11, x_10);
lean_dec(x_11);
x_16 = l_Lean_Syntax_matchesNull(x_15, x_10);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_array_uset(x_3, x_2, x_10);
x_20 = l_Lean_Syntax_getArg(x_6, x_18);
lean_dec(x_6);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_19, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; uint8_t x_7; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = 1;
x_12 = lean_array_uget_borrowed(x_2, x_3);
x_13 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__2));
lean_inc(x_12);
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__4));
lean_inc(x_12);
x_16 = l_Lean_Syntax_isOfKind(x_12, x_15);
if (x_16 == 0)
{
x_7 = x_14;
goto block_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
x_19 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___closed__6));
x_20 = l_Lean_Syntax_matchesIdent(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
x_7 = x_14;
goto block_11;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = l_Lean_Syntax_getArg(x_12, x_21);
x_23 = l_Lean_Syntax_matchesNull(x_22, x_21);
if (x_23 == 0)
{
x_7 = x_14;
goto block_11;
}
else
{
x_7 = x_1;
goto block_11;
}
}
}
}
else
{
x_7 = x_1;
goto block_11;
}
block_11:
{
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_6;
}
}
}
else
{
uint8_t x_24; 
x_24 = 0;
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__2(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_22; 
x_14 = lean_ctor_get(x_5, 1);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_5, 0);
lean_dec(x_23);
x_15 = x_5;
x_16 = x_22;
goto block_21;
}
else
{
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(x_1);
if (x_16 == 0)
{
lean_ctor_set(x_15, 0, x_17);
x_18 = x_15;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_14);
x_18 = x_20;
goto block_19;
}
block_19:
{
x_6 = x_18;
goto block_10;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_34; 
x_24 = lean_ctor_get(x_5, 1);
x_34 = !lean_is_exclusive(x_5);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_5, 0);
lean_dec(x_35);
x_25 = x_5;
x_26 = x_34;
goto block_33;
}
else
{
lean_inc(x_24);
lean_dec(x_5);
x_25 = lean_box(0);
x_26 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_27);
x_28 = lean_array_push(x_24, x_27);
x_29 = lean_box(x_11);
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_28);
lean_ctor_set(x_25, 0, x_29);
x_30 = x_25;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_28);
x_30 = x_32;
goto block_31;
}
block_31:
{
x_6 = x_30;
goto block_10;
}
}
}
}
else
{
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__2(x_6, x_2, x_7, x_8, x_5);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_109; lean_object* x_130; uint8_t x_131; 
x_130 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__15_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_));
lean_inc(x_2);
x_131 = l_Lean_Syntax_Stack_matches(x_2, x_130);
if (x_131 == 0)
{
x_109 = x_131;
goto block_129;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_unsigned_to_nat(3u);
x_133 = l_List_get_x3fInternal___redArg(x_2, x_132);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_dec(x_2);
x_134 = 0;
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_));
lean_inc(x_136);
x_138 = l_Lean_Syntax_isOfKind(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__1_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_));
x_140 = l_Lean_Syntax_isOfKind(x_136, x_139);
x_109 = x_140;
goto block_129;
}
else
{
lean_dec(x_136);
x_109 = x_138;
goto block_129;
}
}
}
block_19:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Syntax_getArg(x_6, x_7);
lean_dec(x_7);
x_11 = l_Lean_Syntax_matchesNull(x_10, x_9);
if (x_11 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(6u);
x_13 = l_Lean_Syntax_getArg(x_6, x_12);
lean_dec(x_6);
x_14 = l_Lean_Syntax_matchesNull(x_13, x_9);
if (x_14 == 0)
{
lean_dec_ref(x_5);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_5);
x_16 = lean_nat_dec_lt(x_9, x_15);
if (x_16 == 0)
{
lean_dec_ref(x_5);
return x_16;
}
else
{
if (x_16 == 0)
{
lean_dec_ref(x_5);
return x_16;
}
else
{
size_t x_17; uint8_t x_18; 
x_17 = lean_usize_of_nat(x_15);
x_18 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__1(x_8, x_5, x_4, x_17);
lean_dec_ref(x_5);
return x_18;
}
}
}
}
}
block_38:
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(4u);
x_31 = l_Lean_Syntax_getArg(x_24, x_30);
x_32 = l_Lean_Syntax_isNone(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_inc(x_31);
x_33 = l_Lean_Syntax_matchesNull(x_31, x_23);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Syntax_getArg(x_31, x_28);
lean_dec(x_31);
x_35 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_));
x_36 = l_Lean_Name_mkStr4(x_29, x_26, x_21, x_35);
x_37 = l_Lean_Syntax_isOfKind(x_34, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec_ref(x_22);
return x_37;
}
else
{
x_4 = x_20;
x_5 = x_22;
x_6 = x_24;
x_7 = x_25;
x_8 = x_27;
x_9 = x_28;
goto block_19;
}
}
}
else
{
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
x_4 = x_20;
x_5 = x_22;
x_6 = x_24;
x_7 = x_25;
x_8 = x_27;
x_9 = x_28;
goto block_19;
}
}
block_57:
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_unsigned_to_nat(3u);
x_50 = l_Lean_Syntax_getArg(x_43, x_49);
x_51 = l_Lean_Syntax_isNone(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_inc(x_50);
x_52 = l_Lean_Syntax_matchesNull(x_50, x_42);
if (x_52 == 0)
{
lean_dec(x_50);
lean_dec_ref(x_48);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = l_Lean_Syntax_getArg(x_50, x_47);
lean_dec(x_50);
x_54 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_));
lean_inc_ref(x_40);
lean_inc_ref(x_45);
lean_inc_ref(x_48);
x_55 = l_Lean_Name_mkStr4(x_48, x_45, x_40, x_54);
x_56 = l_Lean_Syntax_isOfKind(x_53, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_dec_ref(x_48);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
return x_56;
}
else
{
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = x_42;
x_24 = x_43;
x_25 = x_44;
x_26 = x_45;
x_27 = x_46;
x_28 = x_47;
x_29 = x_48;
goto block_38;
}
}
}
else
{
lean_dec(x_50);
x_20 = x_39;
x_21 = x_40;
x_22 = x_41;
x_23 = x_42;
x_24 = x_43;
x_25 = x_44;
x_26 = x_45;
x_27 = x_46;
x_28 = x_47;
x_29 = x_48;
goto block_38;
}
}
block_76:
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = lean_array_size(x_66);
x_68 = 0;
x_69 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0(x_67, x_68, x_66);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec_ref(x_65);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_58);
x_70 = 0;
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = lean_unsigned_to_nat(2u);
x_73 = l_Lean_Syntax_getArg(x_60, x_72);
x_74 = l_Lean_Syntax_isNone(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Syntax_matchesNull(x_73, x_59);
if (x_75 == 0)
{
lean_dec(x_71);
lean_dec_ref(x_65);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_58);
return x_75;
}
else
{
x_39 = x_68;
x_40 = x_58;
x_41 = x_71;
x_42 = x_59;
x_43 = x_60;
x_44 = x_62;
x_45 = x_61;
x_46 = x_64;
x_47 = x_63;
x_48 = x_65;
goto block_57;
}
}
else
{
lean_dec(x_73);
x_39 = x_68;
x_40 = x_58;
x_41 = x_71;
x_42 = x_59;
x_43 = x_60;
x_44 = x_62;
x_45 = x_61;
x_46 = x_64;
x_47 = x_63;
x_48 = x_65;
goto block_57;
}
}
}
block_108:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_unsigned_to_nat(1u);
x_85 = l_Lean_Syntax_getArg(x_78, x_84);
lean_inc(x_85);
x_86 = l_Lean_Syntax_matchesNull(x_85, x_84);
if (x_86 == 0)
{
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = l_Lean_Syntax_getArg(x_85, x_82);
lean_dec(x_85);
x_88 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__0___closed__0));
x_89 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_));
lean_inc_ref(x_80);
lean_inc_ref(x_83);
x_90 = l_Lean_Name_mkStr4(x_83, x_80, x_88, x_89);
lean_inc(x_87);
x_91 = l_Lean_Syntax_isOfKind(x_87, x_90);
lean_dec(x_90);
if (x_91 == 0)
{
lean_dec(x_87);
lean_dec_ref(x_83);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec_ref(x_77);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = l_Lean_Syntax_getArg(x_87, x_84);
lean_dec(x_87);
x_93 = l_Lean_Syntax_getArgs(x_92);
lean_dec(x_92);
x_94 = lean_mk_empty_array_with_capacity(x_82);
x_95 = lean_array_get_size(x_93);
x_96 = lean_nat_dec_lt(x_82, x_95);
if (x_96 == 0)
{
lean_dec_ref(x_93);
x_58 = x_77;
x_59 = x_84;
x_60 = x_78;
x_61 = x_80;
x_62 = x_79;
x_63 = x_82;
x_64 = x_81;
x_65 = x_83;
x_66 = x_94;
goto block_76;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_box(x_81);
lean_inc_ref(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
x_99 = lean_nat_dec_le(x_95, x_95);
if (x_99 == 0)
{
if (x_96 == 0)
{
lean_dec_ref(x_98);
lean_dec_ref(x_93);
x_58 = x_77;
x_59 = x_84;
x_60 = x_78;
x_61 = x_80;
x_62 = x_79;
x_63 = x_82;
x_64 = x_81;
x_65 = x_83;
x_66 = x_94;
goto block_76;
}
else
{
size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_94);
x_100 = 0;
x_101 = lean_usize_of_nat(x_95);
x_102 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__2(x_81, x_93, x_100, x_101, x_98);
lean_dec_ref(x_93);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_58 = x_77;
x_59 = x_84;
x_60 = x_78;
x_61 = x_80;
x_62 = x_79;
x_63 = x_82;
x_64 = x_81;
x_65 = x_83;
x_66 = x_103;
goto block_76;
}
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_94);
x_104 = 0;
x_105 = lean_usize_of_nat(x_95);
x_106 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2__spec__2(x_81, x_93, x_104, x_105, x_98);
lean_dec_ref(x_93);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_58 = x_77;
x_59 = x_84;
x_60 = x_78;
x_61 = x_80;
x_62 = x_79;
x_63 = x_82;
x_64 = x_81;
x_65 = x_83;
x_66 = x_107;
goto block_76;
}
}
}
}
}
block_129:
{
if (x_109 == 0)
{
lean_dec(x_2);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_unsigned_to_nat(5u);
x_111 = l_List_get_x3fInternal___redArg(x_2, x_110);
lean_dec(x_2);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = 0;
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec_ref(x_111);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_unsigned_to_nat(0u);
x_116 = l_Lean_Syntax_getArg(x_114, x_115);
lean_dec(x_114);
x_117 = ((lean_object*)(l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_));
x_118 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__3_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_));
x_119 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_));
x_120 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_));
lean_inc(x_116);
x_121 = l_Lean_Syntax_isOfKind(x_116, x_120);
if (x_121 == 0)
{
lean_dec(x_116);
return x_121;
}
else
{
lean_object* x_122; uint8_t x_123; 
x_122 = l_Lean_Syntax_getArg(x_116, x_115);
x_123 = l_Lean_Syntax_isNone(x_122);
if (x_123 == 0)
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_unsigned_to_nat(1u);
lean_inc(x_122);
x_125 = l_Lean_Syntax_matchesNull(x_122, x_124);
if (x_125 == 0)
{
lean_dec(x_122);
lean_dec(x_116);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_126 = l_Lean_Syntax_getArg(x_122, x_115);
lean_dec(x_122);
x_127 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_));
x_128 = l_Lean_Syntax_isOfKind(x_126, x_127);
if (x_128 == 0)
{
lean_dec(x_116);
return x_128;
}
else
{
x_77 = x_119;
x_78 = x_116;
x_79 = x_110;
x_80 = x_118;
x_81 = x_109;
x_82 = x_115;
x_83 = x_117;
goto block_108;
}
}
}
else
{
lean_dec(x_122);
x_77 = x_119;
x_78 = x_116;
x_79 = x_110;
x_80 = x_118;
x_81 = x_109;
x_82 = x_115;
x_83 = x_117;
goto block_108;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_));
x_5 = l_Lean_Syntax_Stack_matches(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Linter_getLinterUnusedVariablesFunArgs(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__6_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_));
lean_inc(x_2);
x_6 = l_Lean_Syntax_Stack_matches(x_2, x_5);
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_List_get_x3fInternal___redArg(x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(5u);
x_14 = l_List_get_x3fInternal___redArg(x_2, x_13);
lean_dec(x_2);
if (lean_obj_tag(x_14) == 0)
{
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_));
x_18 = l_Lean_Syntax_isOfKind(x_16, x_17);
if (x_18 == 0)
{
return x_12;
}
else
{
return x_4;
}
}
}
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = 0;
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Linter_getLinterUnusedVariablesFunArgs(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__2_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_));
lean_inc(x_2);
x_6 = l_Lean_Syntax_Stack_matches(x_2, x_5);
if (x_6 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(3u);
x_8 = l_List_get_x3fInternal___redArg(x_2, x_7);
lean_dec(x_2);
if (lean_obj_tag(x_8) == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(x_14, 0, x_10);
x_15 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1___closed__4_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_));
x_16 = l_List_any___redArg(x_15, x_14);
return x_16;
}
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Linter_getLinterUnusedVariablesFunArgs(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_));
lean_inc(x_2);
x_6 = l_Lean_Syntax_Stack_matches(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__8_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_));
x_8 = l_Lean_Syntax_Stack_matches(x_2, x_7);
return x_8;
}
else
{
lean_dec(x_2);
return x_6;
}
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_10; uint8_t x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_10 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__4_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_));
lean_inc(x_2);
x_11 = l_Lean_Syntax_isOfKind(x_2, x_10);
if (x_11 == 0)
{
x_4 = x_11;
goto block_9;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_3, x_12);
x_4 = x_13;
goto block_9;
}
block_9:
{
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0___closed__2_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_));
x_6 = l_Lean_Syntax_isOfKind(x_2, x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_dec_eq(x_3, x_7);
lean_dec(x_3);
return x_8;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Linter_getLinterUnusedVariablesPatternVars(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_List_any___redArg(x_3, x_1);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_7 = 0;
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_));
x_3 = l_Lean_Linter_addBuiltinUnusedVariablesIgnoreFn(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Array_instInhabited(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__0, &l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__0_once, _init_l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Linter_unusedVariablesIgnoreFnsExt;
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_obj_once(&l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__1, &l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__1_once, _init_l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___closed__1);
x_9 = lean_box(0);
x_10 = l_Lean_PersistentEnvExtension_getState___redArg(x_8, x_5, x_4, x_7, x_9);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getUnusedVariablesIgnoreFns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Linter_getUnusedVariablesIgnoreFns(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg(size_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_unbox_usize(x_4);
x_7 = lean_usize_dec_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_29; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
x_6 = x_2;
x_7 = x_29;
goto block_28;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_8; size_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unbox_usize(x_3);
x_10 = lean_usize_to_uint64(x_9);
x_11 = 32;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = 16;
x_15 = lean_uint64_shift_right(x_13, x_14);
x_16 = lean_uint64_xor(x_13, x_15);
x_17 = lean_uint64_to_usize(x_16);
x_18 = lean_usize_of_nat(x_8);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
x_21 = lean_usize_land(x_17, x_20);
x_22 = lean_array_uget_borrowed(x_1, x_21);
lean_inc(x_22);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_22);
x_23 = x_6;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_22);
x_23 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_24; 
x_24 = lean_array_uset(x_1, x_21, x_23);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_to_uint64(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget_borrowed(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_42; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 0);
lean_dec(x_44);
x_21 = x_1;
x_22 = x_42;
goto block_41;
}
else
{
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
x_25 = lean_box_usize(x_2);
lean_inc(x_19);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_24, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2___redArg(x_27);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_34);
lean_ctor_set(x_21, 0, x_24);
x_35 = x_21;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_34);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
else
{
lean_object* x_38; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_27);
lean_ctor_set(x_21, 0, x_24);
x_38 = x_21;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_27);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_dec(x_3);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___redArg(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___redArg(lean_object* x_1, size_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_to_uint64(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___redArg(x_1, x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; size_t x_5; uint8_t x_6; 
x_4 = lean_st_ref_get(x_1);
x_5 = lean_ptr_addr(x_2);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___redArg(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_take(x_1);
x_8 = lean_box(0);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___redArg(x_7, x_5, x_8);
x_10 = lean_st_ref_set(x_1, x_9);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Linter_UnusedVariables_insertObjImpl___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_UnusedVariables_insertObjImpl___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_insertObjImpl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_UnusedVariables_insertObjImpl(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_5 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0(x_1, x_2, x_4);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__0_spec__0(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Linter_UnusedVariables_insertObjImpl_spec__1_spec__2_spec__3_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_instHashableFVarId_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_instHashableFVarId_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget_borrowed(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_41; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_1, 0);
lean_dec(x_43);
x_21 = x_1;
x_22 = x_41;
goto block_40;
}
else
{
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_19);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_19);
x_26 = lean_array_uset(x_5, x_18, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1___redArg(x_26);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_33);
lean_ctor_set(x_21, 0, x_24);
x_34 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_24);
x_37 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_st_ref_take(x_1);
x_6 = lean_box(0);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0___redArg(x_5, x_4, x_6);
x_8 = lean_st_ref_set(x_1, x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_Expr_hasFVar(x_2);
lean_dec_ref(x_2);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___lam__0(x_1, x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_expr_eqv(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__9___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10_spec__11___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_Expr_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__9___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_14; lean_object* x_15; 
x_14 = lean_st_ref_get(x_3);
x_15 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___redArg(x_14, x_2);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_inc_ref(x_1);
lean_inc_ref(x_2);
x_16 = lean_apply_2(x_1, x_2, lean_box(0));
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_24 = lean_unbox(x_17);
lean_dec(x_17);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_1);
x_25 = lean_box(0);
x_5 = x_25;
goto block_10;
}
else
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_27);
lean_inc_ref(x_26);
x_18 = x_26;
x_19 = x_27;
x_20 = x_3;
goto block_23;
}
case 6:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_29);
lean_inc_ref(x_28);
x_18 = x_28;
x_19 = x_29;
x_20 = x_3;
goto block_23;
}
case 8:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
lean_inc_ref(x_30);
lean_inc_ref(x_1);
x_33 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_30, x_3);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec_ref(x_33);
lean_inc_ref(x_31);
lean_inc_ref(x_1);
x_34 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_31, x_3);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
lean_inc_ref(x_32);
x_35 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_32, x_3);
x_11 = x_35;
goto block_13;
}
else
{
lean_dec_ref(x_1);
x_11 = x_34;
goto block_13;
}
}
else
{
lean_dec_ref(x_1);
x_11 = x_33;
goto block_13;
}
}
case 5:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_36);
lean_inc_ref(x_1);
x_38 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_36, x_3);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_38);
lean_inc_ref(x_37);
x_39 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_37, x_3);
x_11 = x_39;
goto block_13;
}
else
{
lean_dec_ref(x_1);
x_11 = x_38;
goto block_13;
}
}
case 10:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_40);
x_41 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_40, x_3);
x_11 = x_41;
goto block_13;
}
case 11:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_42);
x_43 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_42, x_3);
x_11 = x_43;
goto block_13;
}
default: 
{
lean_object* x_44; 
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_5 = x_44;
goto block_10;
}
}
}
block_23:
{
lean_object* x_21; 
lean_inc_ref(x_1);
x_21 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_18, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec_ref(x_21);
x_22 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_19, x_20);
x_11 = x_22;
goto block_13;
}
else
{
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_11 = x_21;
goto block_13;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_52; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = lean_ctor_get(x_16, 0);
x_52 = !lean_is_exclusive(x_16);
if (x_52 == 0)
{
x_46 = x_16;
x_47 = x_52;
goto block_51;
}
else
{
lean_inc(x_45);
lean_dec(x_16);
x_46 = lean_box(0);
x_47 = x_52;
goto block_51;
}
block_51:
{
lean_object* x_48; 
if (x_47 == 0)
{
x_48 = x_46;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_48 = x_50;
goto block_49;
}
block_49:
{
return x_48;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_60; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_15, 0);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
x_54 = x_15;
x_55 = x_60;
goto block_59;
}
else
{
lean_inc(x_53);
lean_dec(x_15);
x_54 = lean_box(0);
x_55 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_56; 
if (x_55 == 0)
{
lean_ctor_set_tag(x_54, 0);
x_56 = x_54;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_st_ref_take(x_3);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4___redArg(x_6, x_2, x_5);
x_8 = lean_st_ref_set(x_3, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
block_13:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_5 = x_12;
goto block_10;
}
else
{
lean_dec_ref(x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_UnusedVariables_insertObjImpl___redArg(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_18; 
x_7 = lean_ctor_get(x_6, 0);
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
x_8 = x_6;
x_9 = x_18;
goto block_17;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_10; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_del_object(x_8);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___lam__0___boxed), 3, 1);
lean_closure_set(x_15, 0, x_2);
x_16 = l_Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1(x_15, x_3, x_4);
return x_16;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_6, 0);
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
x_20 = x_6;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__3_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__7(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__9___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1_spec__2_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_ForEachExpr_visit___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__1_spec__4_spec__8_spec__10_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_11);
lean_inc(x_2);
x_12 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr(x_1, x_2, x_11, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__1(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_UnusedVariables_insertObjImpl___redArg(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_42; 
x_7 = lean_ctor_get(x_6, 0);
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
x_8 = x_6;
x_9 = x_42;
goto block_41;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_42;
goto block_41;
}
block_41:
{
uint8_t x_10; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_11 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
lean_del_object(x_8);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_box(0);
x_17 = lean_array_size(x_15);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__0(x_1, x_2, x_15, x_17, x_18, x_16, x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_20 = x_19;
x_21 = x_26;
goto block_25;
}
else
{
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_16);
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_16);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
else
{
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_box(0);
x_30 = lean_array_size(x_28);
x_31 = 0;
x_32 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__1(x_1, x_2, x_28, x_30, x_31, x_29, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; uint8_t x_39; 
x_39 = !lean_is_exclusive(x_32);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_32, 0);
lean_dec(x_40);
x_33 = x_32;
x_34 = x_39;
goto block_38;
}
else
{
lean_dec(x_32);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_29);
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_29);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
else
{
return x_32;
}
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_50; 
lean_dec(x_2);
x_43 = lean_ctor_get(x_6, 0);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
x_44 = x_6;
x_45 = x_50;
goto block_49;
}
else
{
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_box(0);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_45 == 0)
{
x_46 = x_44;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_UnusedVariables_insertObjImpl___redArg(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_24; 
x_7 = lean_ctor_get(x_6, 0);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
x_8 = x_6;
x_9 = x_24;
goto block_23;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_24;
goto block_23;
}
block_23:
{
uint8_t x_10; 
x_10 = lean_unbox(x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_11);
x_12 = x_8;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
else
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_15; lean_object* x_16; 
lean_del_object(x_8);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr(x_1, x_2, x_15, x_4);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; 
lean_del_object(x_8);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec_ref(x_3);
x_18 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode(x_1, x_2, x_17, x_4);
lean_dec(x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_19);
x_20 = x_8;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_6, 0);
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
x_26 = x_6;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_11);
lean_inc(x_2);
x_12 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitEntry(x_1, x_2, x_11, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitEntry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitEntry(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_visitAssignments_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_5, x_4);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget_borrowed(x_3, x_5);
lean_inc(x_2);
x_12 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitNode(x_1, x_2, x_11, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec_ref(x_12);
x_13 = lean_box(0);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_6 = x_13;
goto _start;
}
else
{
lean_dec(x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_visitAssignments_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_visitAssignments_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Linter_UnusedVariables_visitAssignments___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Linter_UnusedVariables_visitAssignments___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Linter_UnusedVariables_visitAssignments___closed__0, &l_Lean_Linter_UnusedVariables_visitAssignments___closed__0_once, _init_l_Lean_Linter_UnusedVariables_visitAssignments___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_visitAssignments(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_obj_once(&l_Lean_Linter_UnusedVariables_visitAssignments___closed__1, &l_Lean_Linter_UnusedVariables_visitAssignments___closed__1_once, _init_l_Lean_Linter_UnusedVariables_visitAssignments___closed__1);
x_6 = lean_st_mk_ref(x_5);
x_11 = lean_box(0);
x_12 = lean_array_size(x_3);
x_13 = 0;
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_visitAssignments_spec__0(x_1, x_2, x_3, x_12, x_13, x_11, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_dec_ref(x_14);
x_7 = x_11;
goto block_10;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_7 = x_15;
goto block_10;
}
else
{
lean_dec(x_6);
return x_14;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_8);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_visitAssignments___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Linter_UnusedVariables_visitAssignments(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_instHashableFVarId_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_followAliases(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_followAliases___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Linter_UnusedVariables_followAliases(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_UnusedVariables_followAliases_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent___closed__1));
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
if (x_3 == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__1(x_1, x_2, x_3, x_7, x_5);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___lam__0(x_4, x_5, x_3);
lean_dec_ref(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = 1;
x_7 = lean_box(x_6);
x_8 = lean_box(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_10);
x_11 = l_Lean_Elab_InfoTree_findInfo_x3f(x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
if (x_1 == 0)
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
goto _start;
}
else
{
return x_6;
}
}
else
{
lean_dec_ref(x_11);
return x_6;
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
return x_6;
}
else
{
if (x_6 == 0)
{
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_5);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3_spec__6(x_1, x_3, x_7, x_8);
return x_9;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_10);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
return x_13;
}
else
{
if (x_13 == 0)
{
return x_13;
}
else
{
size_t x_14; size_t x_15; uint8_t x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_12);
x_16 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4(x_1, x_10, x_14, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3_spec__6(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget_borrowed(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3(x_1, x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3_spec__6(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_PersistentArray_anyMAux___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__3(x_1, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
if (x_8 == 0)
{
return x_5;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2_spec__4(x_1, x_4, x_9, x_10);
return x_11;
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = l_Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2(x_3, x_2);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_Syntax_instBEqRange_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Syntax_instHashableRange_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = l_Lean_instBEqMVarId_beq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2_spec__10___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = l_Lean_instBEqMVarId_beq(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_instHashableMVarId_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_instHashableMVarId_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6_spec__13___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6_spec__13___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_instHashableFVarId_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__1___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6_spec__13___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11_spec__18___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Syntax_instHashableRange_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11_spec__18___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_Syntax_instBEqRange_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = l_Lean_Syntax_instBEqRange_beq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5_spec__11___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_Syntax_instHashableRange_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5_spec__11___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_Syntax_instHashableRange_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget_borrowed(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg(x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_41; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_1, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_1, 0);
lean_dec(x_43);
x_21 = x_1;
x_22 = x_41;
goto block_40;
}
else
{
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_19);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_19);
x_26 = lean_array_uset(x_5, x_18, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7___redArg(x_26);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_33);
lean_ctor_set(x_21, 0, x_24);
x_34 = x_21;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_24);
x_37 = x_21;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(x_6);
x_10 = lean_apply_6(x_1, x_2, x_3, x_4, x_9, x_7, lean_box(0));
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___lam__0(x_1, x_2, x_3, x_4, x_5, x_9, x_7);
lean_dec(x_5);
return x_10;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0);
x_6 = l_ReaderT_instMonad___redArg(x_5);
x_7 = l_ReaderT_instMonad___redArg(x_6);
x_8 = lean_box(0);
x_9 = l_instInhabitedOfMonad___redArg(x_7, x_8);
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_box(x_2);
x_12 = lean_apply_3(x_10, x_11, x_3, lean_box(0));
return x_12;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg(x_1, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__2));
x_2 = lean_unsigned_to_nat(21u);
x_3 = lean_unsigned_to_nat(65u);
x_4 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_4);
x_10 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_8, x_3);
x_3 = x_10;
x_4 = x_9;
goto _start;
}
case 1:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3);
x_13 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg(x_12, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_4);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_box(x_5);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_16);
x_18 = lean_apply_6(x_1, x_16, x_14, x_15, x_17, x_6, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_46; 
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_3);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_3, 0);
lean_dec(x_47);
x_21 = x_3;
x_22 = x_46;
goto block_45;
}
else
{
lean_dec(x_3);
x_21 = lean_box(0);
x_22 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_box(0);
x_24 = lean_box(x_5);
x_25 = lean_apply_7(x_2, x_16, x_14, x_15, x_23, x_24, x_6, lean_box(0));
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_26 = lean_ctor_get(x_25, 0);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
x_27 = x_25;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_29; 
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_26);
x_29 = x_21;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_26);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_29);
x_30 = x_27;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_del_object(x_21);
x_37 = lean_ctor_get(x_25, 0);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
x_38 = x_25;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Lean_Elab_Info_updateContext_x3f(x_3, x_14);
x_49 = l_Lean_PersistentArray_toList___redArg(x_15);
x_50 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_2);
x_51 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___redArg(x_1, x_2, x_48, x_49, x_50, x_5, x_6);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_box(x_5);
x_54 = lean_apply_7(x_2, x_16, x_14, x_15, x_52, x_53, x_6, lean_box(0));
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_63; 
x_55 = lean_ctor_get(x_54, 0);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
x_56 = x_54;
x_57 = x_63;
goto block_62;
}
else
{
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_55);
if (x_57 == 0)
{
lean_ctor_set(x_56, 0, x_58);
x_59 = x_56;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_58);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
x_64 = lean_ctor_get(x_54, 0);
x_71 = !lean_is_exclusive(x_54);
if (x_71 == 0)
{
x_65 = x_54;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_54);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_2);
x_72 = lean_ctor_get(x_51, 0);
x_79 = !lean_is_exclusive(x_51);
if (x_79 == 0)
{
x_73 = x_51;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_51);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_80 = lean_ctor_get(x_18, 0);
x_87 = !lean_is_exclusive(x_18);
if (x_87 == 0)
{
x_81 = x_18;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_18);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
}
default: 
{
lean_object* x_88; uint8_t x_89; uint8_t x_95; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_4);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_4, 0);
lean_dec(x_96);
x_88 = x_4;
x_89 = x_95;
goto block_94;
}
else
{
lean_dec(x_4);
x_88 = lean_box(0);
x_89 = x_95;
goto block_94;
}
block_94:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_box(0);
if (x_89 == 0)
{
lean_ctor_set_tag(x_88, 0);
lean_ctor_set(x_88, 0, x_90);
x_91 = x_88;
goto block_92;
}
else
{
lean_object* x_93; 
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_91 = x_93;
goto block_92;
}
block_92:
{
return x_91;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = l_List_reverse___redArg(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_30; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
x_13 = x_4;
x_14 = x_30;
goto block_29;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_15; 
lean_inc(x_7);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg(x_1, x_2, x_3, x_11, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 0, x_16);
x_17 = x_13;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_5);
x_17 = x_20;
goto block_19;
}
block_19:
{
x_4 = x_12;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_22 = x_15;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___redArg(x_1, x_2, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg(x_1, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___lam__0___boxed), 8, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg(x_1, x_8, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_10 = x_9;
x_11 = x_17;
goto block_16;
}
else
{
lean_dec(x_9);
x_10 = lean_box(0);
x_11 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_12);
x_13 = x_10;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_19 = lean_ctor_get(x_9, 0);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_20 = x_9;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7(x_1, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__2));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
switch (lean_obj_tag(x_5)) {
case 10:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_96; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_5, 0);
x_96 = !lean_is_exclusive(x_5);
if (x_96 == 0)
{
x_18 = x_5;
x_19 = x_96;
goto block_95;
}
else
{
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_box(0);
x_19 = x_96;
goto block_95;
}
block_95:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_16, 3);
x_21 = lean_ctor_get(x_16, 4);
x_22 = l_Lean_Linter_linter_unusedVariables_analyzeTactics;
x_23 = l_Lean_Option_get___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__0(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_dec_ref(x_17);
x_44 = l_Lean_Elab_Term_instImpl_00___x40_Lean_Elab_Term_TermElabM_4118479936____hygCtx___hyg_9_;
x_45 = l___private_Init_Dynamic_0__Dynamic_get_x3fImpl___redArg(x_43, x_44);
lean_dec(x_43);
if (lean_obj_tag(x_45) == 1)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_86; 
lean_del_object(x_18);
x_46 = lean_ctor_get(x_45, 0);
x_86 = !lean_is_exclusive(x_45);
if (x_86 == 0)
{
x_47 = x_45;
x_48 = x_86;
goto block_85;
}
else
{
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = x_86;
goto block_85;
}
block_85:
{
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_80; 
lean_del_object(x_47);
x_49 = lean_ctor_get(x_46, 0);
x_80 = !lean_is_exclusive(x_46);
if (x_80 == 0)
{
x_50 = x_46;
x_51 = x_80;
goto block_79;
}
else
{
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_78; 
lean_inc_ref(x_20);
x_52 = l_Lean_instantiateMVarsCore(x_20, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_st_ref_take(x_8);
x_55 = lean_ctor_get(x_54, 0);
x_56 = lean_ctor_get(x_54, 1);
x_57 = lean_ctor_get(x_54, 2);
x_58 = lean_ctor_get(x_54, 3);
x_59 = lean_ctor_get(x_54, 4);
x_78 = !lean_is_exclusive(x_54);
if (x_78 == 0)
{
x_60 = x_54;
x_61 = x_78;
goto block_77;
}
else
{
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_54);
x_60 = lean_box(0);
x_61 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__1);
x_63 = lean_box(0);
x_64 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1___redArg(x_62, x_63, x_53);
x_65 = lean_array_push(x_59, x_64);
if (x_61 == 0)
{
lean_ctor_set(x_60, 4, x_65);
x_66 = x_60;
goto block_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_76, 0, x_55);
lean_ctor_set(x_76, 1, x_56);
lean_ctor_set(x_76, 2, x_57);
lean_ctor_set(x_76, 3, x_58);
lean_ctor_set(x_76, 4, x_65);
x_66 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_st_ref_set(x_8, x_66);
x_68 = l_Lean_PersistentArray_toArray___redArg(x_6);
if (x_51 == 0)
{
lean_ctor_set(x_50, 0, x_4);
x_69 = x_50;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_4);
x_69 = x_74;
goto block_73;
}
block_73:
{
if (x_7 == 0)
{
uint8_t x_70; lean_object* x_71; 
x_70 = l_Lean_PersistentArray_anyM___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__2(x_23, x_6);
x_71 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go(x_1, x_2, x_68, x_69, x_70, x_8);
lean_dec_ref(x_68);
x_24 = x_71;
goto block_42;
}
else
{
lean_object* x_72; 
x_72 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go(x_1, x_2, x_68, x_69, x_7, x_8);
lean_dec_ref(x_68);
x_24 = x_72;
goto block_42;
}
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_81 = lean_box(x_3);
if (x_48 == 0)
{
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_81);
x_82 = x_47;
goto block_83;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_81);
x_82 = x_84;
goto block_83;
}
block_83:
{
return x_82;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_87 = lean_box(x_3);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_87);
x_88 = x_18;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_87);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_17);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_91 = lean_box(x_3);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_91);
x_92 = x_18;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
block_42:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; uint8_t x_32; 
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_24, 0);
lean_dec(x_33);
x_25 = x_24;
x_26 = x_32;
goto block_31;
}
else
{
lean_dec(x_24);
x_25 = lean_box(0);
x_26 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(x_23);
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_27);
x_28 = x_25;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_34 = lean_ctor_get(x_24, 0);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
x_35 = x_24;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
case 1:
{
if (x_7 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_5, 0);
x_98 = lean_ctor_get(x_97, 3);
switch (lean_obj_tag(x_98)) {
case 4:
{
uint8_t x_99; 
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_99 = lean_ctor_get_uint8(x_97, sizeof(void*)*4);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; uint8_t x_107; 
lean_dec(x_8);
x_107 = !lean_is_exclusive(x_5);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_5, 0);
lean_dec(x_108);
x_100 = x_5;
x_101 = x_107;
goto block_106;
}
else
{
lean_dec(x_5);
x_100 = lean_box(0);
x_101 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_box(x_3);
if (x_101 == 0)
{
lean_ctor_set_tag(x_100, 0);
lean_ctor_set(x_100, 0, x_102);
x_103 = x_100;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_102);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
else
{
lean_object* x_109; 
x_109 = l_Lean_Elab_Info_range_x3f(x_5);
if (lean_obj_tag(x_109) == 1)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_140; 
x_110 = lean_ctor_get(x_109, 0);
x_140 = !lean_is_exclusive(x_109);
if (x_140 == 0)
{
x_111 = x_109;
x_112 = x_140;
goto block_139;
}
else
{
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_box(0);
x_112 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Lean_Elab_Info_stx(x_5);
lean_dec_ref(x_5);
x_114 = l_Lean_Syntax_getHeadInfo(x_113);
lean_dec(x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_134; 
lean_dec_ref(x_114);
x_115 = lean_st_ref_take(x_8);
x_116 = lean_ctor_get(x_115, 0);
x_117 = lean_ctor_get(x_115, 1);
x_118 = lean_ctor_get(x_115, 2);
x_119 = lean_ctor_get(x_115, 3);
x_120 = lean_ctor_get(x_115, 4);
x_134 = !lean_is_exclusive(x_115);
if (x_134 == 0)
{
x_121 = x_115;
x_122 = x_134;
goto block_133;
}
else
{
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_115);
x_121 = lean_box(0);
x_122 = x_134;
goto block_133;
}
block_133:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_box(0);
x_124 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3___redArg(x_116, x_110, x_123);
if (x_122 == 0)
{
lean_ctor_set(x_121, 0, x_124);
x_125 = x_121;
goto block_131;
}
else
{
lean_object* x_132; 
x_132 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_132, 0, x_124);
lean_ctor_set(x_132, 1, x_117);
lean_ctor_set(x_132, 2, x_118);
lean_ctor_set(x_132, 3, x_119);
lean_ctor_set(x_132, 4, x_120);
x_125 = x_132;
goto block_131;
}
block_131:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_st_ref_set(x_8, x_125);
lean_dec(x_8);
x_127 = lean_box(x_3);
if (x_112 == 0)
{
lean_ctor_set_tag(x_111, 0);
lean_ctor_set(x_111, 0, x_127);
x_128 = x_111;
goto block_129;
}
else
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_127);
x_128 = x_130;
goto block_129;
}
block_129:
{
return x_128;
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_114);
lean_dec(x_110);
lean_dec(x_8);
x_135 = lean_box(x_99);
if (x_112 == 0)
{
lean_ctor_set_tag(x_111, 0);
lean_ctor_set(x_111, 0, x_135);
x_136 = x_111;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_135);
x_136 = x_138;
goto block_137;
}
block_137:
{
return x_136;
}
}
}
}
else
{
lean_object* x_141; uint8_t x_142; uint8_t x_148; 
lean_dec(x_109);
lean_dec(x_8);
x_148 = !lean_is_exclusive(x_5);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_5, 0);
lean_dec(x_149);
x_141 = x_5;
x_142 = x_148;
goto block_147;
}
else
{
lean_dec(x_5);
x_141 = lean_box(0);
x_142 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_box(x_99);
if (x_142 == 0)
{
lean_ctor_set_tag(x_141, 0);
lean_ctor_set(x_141, 0, x_143);
x_144 = x_141;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_143);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
}
case 1:
{
lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_97, 1);
x_151 = lean_ctor_get_uint8(x_97, sizeof(void*)*4);
x_152 = lean_ctor_get(x_98, 0);
x_153 = l_Lean_Elab_Info_range_x3f(x_5);
if (lean_obj_tag(x_153) == 1)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_275; 
lean_inc(x_152);
lean_inc_ref(x_150);
x_154 = lean_ctor_get(x_153, 0);
x_275 = !lean_is_exclusive(x_153);
if (x_275 == 0)
{
x_155 = x_153;
x_156 = x_275;
goto block_274;
}
else
{
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_box(0);
x_156 = x_275;
goto block_274;
}
block_274:
{
lean_object* x_157; lean_object* x_158; 
x_157 = l_Lean_Elab_Info_stx(x_5);
lean_dec_ref(x_5);
x_158 = l_Lean_Syntax_getHeadInfo(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; uint8_t x_160; uint8_t x_265; 
x_265 = !lean_is_exclusive(x_158);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_158, 3);
lean_dec(x_266);
x_267 = lean_ctor_get(x_158, 2);
lean_dec(x_267);
x_268 = lean_ctor_get(x_158, 1);
lean_dec(x_268);
x_269 = lean_ctor_get(x_158, 0);
lean_dec(x_269);
x_159 = x_158;
x_160 = x_265;
goto block_264;
}
else
{
lean_dec(x_158);
x_159 = lean_box(0);
x_160 = x_265;
goto block_264;
}
block_264:
{
if (x_151 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_180; 
lean_del_object(x_159);
lean_dec(x_157);
lean_dec(x_154);
lean_dec_ref(x_150);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_161 = lean_st_ref_take(x_8);
x_162 = lean_ctor_get(x_161, 0);
x_163 = lean_ctor_get(x_161, 1);
x_164 = lean_ctor_get(x_161, 2);
x_165 = lean_ctor_get(x_161, 3);
x_166 = lean_ctor_get(x_161, 4);
x_180 = !lean_is_exclusive(x_161);
if (x_180 == 0)
{
x_167 = x_161;
x_168 = x_180;
goto block_179;
}
else
{
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_161);
x_167 = lean_box(0);
x_168 = x_180;
goto block_179;
}
block_179:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_box(0);
x_170 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0___redArg(x_164, x_152, x_169);
if (x_168 == 0)
{
lean_ctor_set(x_167, 2, x_170);
x_171 = x_167;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_178, 0, x_162);
lean_ctor_set(x_178, 1, x_163);
lean_ctor_set(x_178, 2, x_170);
lean_ctor_set(x_178, 3, x_165);
lean_ctor_set(x_178, 4, x_166);
x_171 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_st_ref_set(x_8, x_171);
lean_dec(x_8);
x_173 = lean_box(x_3);
if (x_156 == 0)
{
lean_ctor_set_tag(x_155, 0);
lean_ctor_set(x_155, 0, x_173);
x_174 = x_155;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_173);
x_174 = x_176;
goto block_175;
}
block_175:
{
return x_174;
}
}
}
}
else
{
lean_object* x_181; 
lean_inc(x_152);
x_181 = lean_local_ctx_find(x_150, x_152);
if (lean_obj_tag(x_181) == 1)
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_259; 
lean_del_object(x_155);
x_182 = lean_ctor_get(x_181, 0);
x_259 = !lean_is_exclusive(x_181);
if (x_259 == 0)
{
x_183 = x_181;
x_184 = x_259;
goto block_258;
}
else
{
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_box(0);
x_184 = x_259;
goto block_258;
}
block_258:
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_154, 0);
x_186 = l_Lean_Syntax_Range_contains(x_1, x_185, x_7);
lean_dec_ref(x_1);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_182);
lean_del_object(x_159);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
x_187 = lean_box(x_151);
if (x_184 == 0)
{
lean_ctor_set_tag(x_183, 0);
lean_ctor_set(x_183, 0, x_187);
x_188 = x_183;
goto block_189;
}
else
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_187);
x_188 = x_190;
goto block_189;
}
block_189:
{
return x_188;
}
}
else
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_LocalDecl_userName(x_182);
lean_dec(x_182);
x_192 = l_Lean_Name_hasMacroScopes(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_193 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_193);
lean_dec_ref(x_4);
x_194 = lean_ctor_get(x_193, 4);
lean_inc_ref(x_194);
lean_dec_ref(x_193);
lean_inc_ref(x_194);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_2);
x_196 = l_Lean_Linter_getLinterUnusedVariables(x_195);
lean_dec_ref(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_194);
lean_dec(x_191);
lean_del_object(x_159);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_8);
x_197 = lean_box(x_151);
if (x_184 == 0)
{
lean_ctor_set_tag(x_183, 0);
lean_ctor_set(x_183, 0, x_197);
x_198 = x_183;
goto block_199;
}
else
{
lean_object* x_200; 
x_200 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_200, 0, x_197);
x_198 = x_200;
goto block_199;
}
block_199:
{
return x_198;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_242; 
x_201 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_skipDeclIdIfPresent(x_157);
x_242 = l_Lean_Syntax_getId(x_201);
if (lean_obj_tag(x_242) == 1)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_243 = lean_ctor_get(x_242, 1);
lean_inc_ref(x_243);
lean_dec_ref(x_242);
x_244 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__2));
x_245 = lean_string_utf8_byte_size(x_243);
x_246 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___closed__3);
x_247 = lean_nat_dec_le(x_246, x_245);
if (x_247 == 0)
{
lean_dec_ref(x_243);
lean_del_object(x_183);
x_202 = x_8;
goto block_241;
}
else
{
lean_object* x_248; uint8_t x_249; 
x_248 = lean_unsigned_to_nat(0u);
x_249 = lean_string_memcmp(x_243, x_244, x_248, x_248, x_246);
lean_dec_ref(x_243);
if (x_249 == 0)
{
lean_del_object(x_183);
x_202 = x_8;
goto block_241;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_201);
lean_dec_ref(x_194);
lean_dec(x_191);
lean_del_object(x_159);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_8);
x_250 = lean_box(x_151);
if (x_184 == 0)
{
lean_ctor_set_tag(x_183, 0);
lean_ctor_set(x_183, 0, x_250);
x_251 = x_183;
goto block_252;
}
else
{
lean_object* x_253; 
x_253 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_253, 0, x_250);
x_251 = x_253;
goto block_252;
}
block_252:
{
return x_251;
}
}
}
}
else
{
lean_dec(x_242);
lean_del_object(x_183);
x_202 = x_8;
goto block_241;
}
block_241:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; uint8_t x_240; 
x_203 = lean_st_ref_take(x_202);
x_204 = lean_ctor_get(x_203, 0);
x_205 = lean_ctor_get(x_203, 1);
x_206 = lean_ctor_get(x_203, 2);
x_207 = lean_ctor_get(x_203, 3);
x_208 = lean_ctor_get(x_203, 4);
x_240 = !lean_is_exclusive(x_203);
if (x_240 == 0)
{
x_209 = x_203;
x_210 = x_240;
goto block_239;
}
else
{
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_203);
x_209 = lean_box(0);
x_210 = x_240;
goto block_239;
}
block_239:
{
lean_object* x_211; 
x_211 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___redArg(x_205, x_154);
if (lean_obj_tag(x_211) == 1)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; uint8_t x_228; 
lean_dec(x_201);
lean_dec_ref(x_194);
lean_dec(x_191);
lean_del_object(x_159);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
x_213 = lean_ctor_get(x_212, 0);
x_214 = lean_ctor_get(x_212, 1);
x_215 = lean_ctor_get(x_212, 2);
x_216 = lean_ctor_get(x_212, 3);
x_228 = !lean_is_exclusive(x_212);
if (x_228 == 0)
{
x_217 = x_212;
x_218 = x_228;
goto block_227;
}
else
{
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_212);
x_217 = lean_box(0);
x_218 = x_228;
goto block_227;
}
block_227:
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_array_push(x_216, x_152);
if (x_218 == 0)
{
lean_ctor_set(x_217, 3, x_219);
x_220 = x_217;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_226, 0, x_213);
lean_ctor_set(x_226, 1, x_214);
lean_ctor_set(x_226, 2, x_215);
lean_ctor_set(x_226, 3, x_219);
x_220 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_221; lean_object* x_222; 
x_221 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5___redArg(x_205, x_154, x_220);
if (x_210 == 0)
{
lean_ctor_set(x_209, 1, x_221);
x_222 = x_209;
goto block_223;
}
else
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_224, 0, x_204);
lean_ctor_set(x_224, 1, x_221);
lean_ctor_set(x_224, 2, x_206);
lean_ctor_set(x_224, 3, x_207);
lean_ctor_set(x_224, 4, x_208);
x_222 = x_224;
goto block_223;
}
block_223:
{
x_10 = x_202;
x_11 = x_222;
goto block_15;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_211);
x_229 = lean_unsigned_to_nat(1u);
x_230 = lean_mk_empty_array_with_capacity(x_229);
x_231 = lean_array_push(x_230, x_152);
if (x_160 == 0)
{
lean_ctor_set(x_159, 3, x_231);
lean_ctor_set(x_159, 2, x_194);
lean_ctor_set(x_159, 1, x_201);
lean_ctor_set(x_159, 0, x_191);
x_232 = x_159;
goto block_237;
}
else
{
lean_object* x_238; 
x_238 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_238, 0, x_191);
lean_ctor_set(x_238, 1, x_201);
lean_ctor_set(x_238, 2, x_194);
lean_ctor_set(x_238, 3, x_231);
x_232 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_233; lean_object* x_234; 
x_233 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5___redArg(x_205, x_154, x_232);
if (x_210 == 0)
{
lean_ctor_set(x_209, 1, x_233);
x_234 = x_209;
goto block_235;
}
else
{
lean_object* x_236; 
x_236 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_236, 0, x_204);
lean_ctor_set(x_236, 1, x_233);
lean_ctor_set(x_236, 2, x_206);
lean_ctor_set(x_236, 3, x_207);
lean_ctor_set(x_236, 4, x_208);
x_234 = x_236;
goto block_235;
}
block_235:
{
x_10 = x_202;
x_11 = x_234;
goto block_15;
}
}
}
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_191);
lean_del_object(x_159);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
x_254 = lean_box(x_151);
if (x_184 == 0)
{
lean_ctor_set_tag(x_183, 0);
lean_ctor_set(x_183, 0, x_254);
x_255 = x_183;
goto block_256;
}
else
{
lean_object* x_257; 
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_254);
x_255 = x_257;
goto block_256;
}
block_256:
{
return x_255;
}
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_181);
lean_del_object(x_159);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_260 = lean_box(x_151);
if (x_156 == 0)
{
lean_ctor_set_tag(x_155, 0);
lean_ctor_set(x_155, 0, x_260);
x_261 = x_155;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_260);
x_261 = x_263;
goto block_262;
}
block_262:
{
return x_261;
}
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_152);
lean_dec_ref(x_150);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_270 = lean_box(x_3);
if (x_156 == 0)
{
lean_ctor_set_tag(x_155, 0);
lean_ctor_set(x_155, 0, x_270);
x_271 = x_155;
goto block_272;
}
else
{
lean_object* x_273; 
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_270);
x_271 = x_273;
goto block_272;
}
block_272:
{
return x_271;
}
}
}
}
else
{
lean_object* x_276; uint8_t x_277; uint8_t x_283; 
lean_dec(x_153);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_283 = !lean_is_exclusive(x_5);
if (x_283 == 0)
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_5, 0);
lean_dec(x_284);
x_276 = x_5;
x_277 = x_283;
goto block_282;
}
else
{
lean_dec(x_5);
x_276 = lean_box(0);
x_277 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_box(x_3);
if (x_277 == 0)
{
lean_ctor_set_tag(x_276, 0);
lean_ctor_set(x_276, 0, x_278);
x_279 = x_276;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_281, 0, x_278);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
}
default: 
{
lean_object* x_285; uint8_t x_286; uint8_t x_292; 
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_292 = !lean_is_exclusive(x_5);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = lean_ctor_get(x_5, 0);
lean_dec(x_293);
x_285 = x_5;
x_286 = x_292;
goto block_291;
}
else
{
lean_dec(x_5);
x_285 = lean_box(0);
x_286 = x_292;
goto block_291;
}
block_291:
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_box(x_3);
if (x_286 == 0)
{
lean_ctor_set_tag(x_285, 0);
lean_ctor_set(x_285, 0, x_287);
x_288 = x_285;
goto block_289;
}
else
{
lean_object* x_290; 
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_287);
x_288 = x_290;
goto block_289;
}
block_289:
{
return x_288;
}
}
}
}
}
else
{
lean_object* x_294; uint8_t x_295; uint8_t x_301; 
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_301 = !lean_is_exclusive(x_5);
if (x_301 == 0)
{
lean_object* x_302; 
x_302 = lean_ctor_get(x_5, 0);
lean_dec(x_302);
x_294 = x_5;
x_295 = x_301;
goto block_300;
}
else
{
lean_dec(x_5);
x_294 = lean_box(0);
x_295 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_box(x_7);
if (x_295 == 0)
{
lean_ctor_set_tag(x_294, 0);
lean_ctor_set(x_294, 0, x_296);
x_297 = x_294;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_299, 0, x_296);
x_297 = x_299;
goto block_298;
}
block_298:
{
return x_297;
}
}
}
}
case 0:
{
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
if (x_7 == 0)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; uint8_t x_328; 
x_303 = lean_ctor_get(x_5, 0);
x_328 = !lean_is_exclusive(x_5);
if (x_328 == 0)
{
x_304 = x_5;
x_305 = x_328;
goto block_327;
}
else
{
lean_inc(x_303);
lean_dec(x_5);
x_304 = lean_box(0);
x_305 = x_328;
goto block_327;
}
block_327:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; uint8_t x_326; 
x_306 = lean_st_ref_take(x_8);
x_307 = lean_ctor_get(x_303, 3);
lean_inc_ref(x_307);
lean_dec_ref(x_303);
x_308 = lean_ctor_get(x_306, 0);
x_309 = lean_ctor_get(x_306, 1);
x_310 = lean_ctor_get(x_306, 2);
x_311 = lean_ctor_get(x_306, 3);
x_312 = lean_ctor_get(x_306, 4);
x_326 = !lean_is_exclusive(x_306);
if (x_326 == 0)
{
x_313 = x_306;
x_314 = x_326;
goto block_325;
}
else
{
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_306);
x_313 = lean_box(0);
x_314 = x_326;
goto block_325;
}
block_325:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_307, 7);
lean_inc_ref(x_315);
lean_dec_ref(x_307);
x_316 = lean_array_push(x_312, x_315);
if (x_314 == 0)
{
lean_ctor_set(x_313, 4, x_316);
x_317 = x_313;
goto block_323;
}
else
{
lean_object* x_324; 
x_324 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_324, 0, x_308);
lean_ctor_set(x_324, 1, x_309);
lean_ctor_set(x_324, 2, x_310);
lean_ctor_set(x_324, 3, x_311);
lean_ctor_set(x_324, 4, x_316);
x_317 = x_324;
goto block_323;
}
block_323:
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_st_ref_set(x_8, x_317);
lean_dec(x_8);
x_319 = lean_box(x_3);
if (x_305 == 0)
{
lean_ctor_set(x_304, 0, x_319);
x_320 = x_304;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_322, 0, x_319);
x_320 = x_322;
goto block_321;
}
block_321:
{
return x_320;
}
}
}
}
}
else
{
lean_object* x_329; uint8_t x_330; uint8_t x_336; 
lean_dec(x_8);
x_336 = !lean_is_exclusive(x_5);
if (x_336 == 0)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_5, 0);
lean_dec(x_337);
x_329 = x_5;
x_330 = x_336;
goto block_335;
}
else
{
lean_dec(x_5);
x_329 = lean_box(0);
x_330 = x_336;
goto block_335;
}
block_335:
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_box(x_7);
if (x_330 == 0)
{
lean_ctor_set(x_329, 0, x_331);
x_332 = x_329;
goto block_333;
}
else
{
lean_object* x_334; 
x_334 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_334, 0, x_331);
x_332 = x_334;
goto block_333;
}
block_333:
{
return x_332;
}
}
}
}
case 11:
{
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
if (x_7 == 0)
{
lean_object* x_338; lean_object* x_339; uint8_t x_340; uint8_t x_364; 
x_338 = lean_ctor_get(x_5, 0);
x_364 = !lean_is_exclusive(x_5);
if (x_364 == 0)
{
x_339 = x_5;
x_340 = x_364;
goto block_363;
}
else
{
lean_inc(x_338);
lean_dec(x_5);
x_339 = lean_box(0);
x_340 = x_364;
goto block_363;
}
block_363:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; uint8_t x_362; 
x_341 = lean_st_ref_take(x_8);
x_342 = lean_ctor_get(x_341, 0);
x_343 = lean_ctor_get(x_341, 1);
x_344 = lean_ctor_get(x_341, 2);
x_345 = lean_ctor_get(x_341, 3);
x_346 = lean_ctor_get(x_341, 4);
x_362 = !lean_is_exclusive(x_341);
if (x_362 == 0)
{
x_347 = x_341;
x_348 = x_362;
goto block_361;
}
else
{
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_341);
x_347 = lean_box(0);
x_348 = x_362;
goto block_361;
}
block_361:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_338, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_338, 2);
lean_inc(x_350);
lean_dec_ref(x_338);
x_351 = l_Lean_Linter_UnusedVariables_followAliases(x_345, x_350);
x_352 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6___redArg(x_345, x_349, x_351);
if (x_348 == 0)
{
lean_ctor_set(x_347, 3, x_352);
x_353 = x_347;
goto block_359;
}
else
{
lean_object* x_360; 
x_360 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_360, 0, x_342);
lean_ctor_set(x_360, 1, x_343);
lean_ctor_set(x_360, 2, x_344);
lean_ctor_set(x_360, 3, x_352);
lean_ctor_set(x_360, 4, x_346);
x_353 = x_360;
goto block_359;
}
block_359:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_st_ref_set(x_8, x_353);
lean_dec(x_8);
x_355 = lean_box(x_3);
if (x_340 == 0)
{
lean_ctor_set_tag(x_339, 0);
lean_ctor_set(x_339, 0, x_355);
x_356 = x_339;
goto block_357;
}
else
{
lean_object* x_358; 
x_358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_358, 0, x_355);
x_356 = x_358;
goto block_357;
}
block_357:
{
return x_356;
}
}
}
}
}
else
{
lean_object* x_365; uint8_t x_366; uint8_t x_372; 
lean_dec(x_8);
x_372 = !lean_is_exclusive(x_5);
if (x_372 == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_5, 0);
lean_dec(x_373);
x_365 = x_5;
x_366 = x_372;
goto block_371;
}
else
{
lean_dec(x_5);
x_365 = lean_box(0);
x_366 = x_372;
goto block_371;
}
block_371:
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_box(x_7);
if (x_366 == 0)
{
lean_ctor_set_tag(x_365, 0);
lean_ctor_set(x_365, 0, x_367);
x_368 = x_365;
goto block_369;
}
else
{
lean_object* x_370; 
x_370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_370, 0, x_367);
x_368 = x_370;
goto block_369;
}
block_369:
{
return x_368;
}
}
}
}
default: 
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_374 = lean_box(x_3);
x_375 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_375, 0, x_374);
return x_375;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_st_ref_set(x_10, x_11);
lean_dec(x_10);
x_13 = lean_box(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_7);
x_12 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_11, x_8);
lean_dec_ref(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_6, x_5);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_box(x_11);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___lam__0___boxed), 9, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
x_15 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___closed__0));
x_16 = lean_array_uget_borrowed(x_4, x_6);
lean_inc(x_9);
lean_inc(x_16);
lean_inc(x_3);
x_17 = l_Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7(x_14, x_15, x_3, x_16, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec_ref(x_17);
x_18 = lean_box(0);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_18;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_3);
x_10 = 0;
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8(x_1, x_2, x_4, x_3, x_9, x_10, x_8, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_12 = x_11;
x_13 = x_18;
goto block_17;
}
else
{
lean_dec(x_11);
x_12 = lean_box(0);
x_13 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_14; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_8);
x_14 = x_12;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_8);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
x_9 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go(x_1, x_2, x_3, x_4, x_8, x_6);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox(x_8);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__8(x_1, x_2, x_3, x_4, x_11, x_12, x_7, x_13, x_9);
lean_dec_ref(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__4_spec__9(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__5_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6_spec__13___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20(x_1, x_2, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
x_10 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15(x_1, x_2, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__3(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_7);
x_11 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__1_spec__1_spec__2_spec__10___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11_spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__7_spec__11_spec__18___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_collectReferences(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = 0;
x_8 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go(x_2, x_3, x_1, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_collectReferences___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_UnusedVariables_collectReferences(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__1));
lean_inc(x_1);
x_3 = l_Lean_Syntax_isOfKind(x_1, x_2);
x_4 = 1;
if (x_3 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__3));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___closed__5));
x_8 = l_Lean_Syntax_isOfKind(x_1, x_7);
if (x_8 == 0)
{
return x_8;
}
else
{
return x_4;
}
}
else
{
lean_dec(x_1);
return x_4;
}
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___lam__0(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___closed__0));
x_3 = l_Lean_Syntax_find_x3f(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec_ref(x_3);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Linter_linterSetsExt;
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_9, x_6, x_5, x_8, x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_instHashableFVarId_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0_spec__0___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg(x_1, x_3);
lean_dec(x_3);
if (x_6 == 0)
{
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0___redArg(x_1, x_4, x_8);
x_1 = x_9;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__21(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__20(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__21(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Syntax_instHashableRange_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__3_spec__6___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget_borrowed(x_1, x_3);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_visitAssignments_visitExpr_spec__0___redArg(x_4, x_6, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9_spec__12(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_array_size(x_2);
x_4 = 0;
x_5 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9_spec__12(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget_borrowed(x_4, x_5);
lean_inc(x_8);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = lean_apply_3(x_8, x_1, x_2, x_3);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_unbox(x_9);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec_ref(x_4);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l_Lean_Syntax_findStack_x3f(x_8, x_1, x_2);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_3);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_4;
}
else
{
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_4;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_13);
x_17 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6(x_5, x_11, x_6, x_3, x_15, x_16);
return x_17;
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_4;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__2(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec_ref(x_3);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getRange_x3f(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
return x_1;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_Syntax_Range_includes(x_5, x_2, x_1, x_1);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_isIdent(x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Syntax_getRange_x3f(x_3, x_1);
if (lean_obj_tag(x_5) == 0)
{
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Syntax_instBEqRange_beq(x_6, x_2);
lean_dec(x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__0(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__10(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_array_push(x_2, x_8);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_array_push(x_2, x_8);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__1));
x_27 = l_List_filterMapTR_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__9(x_5, x_26);
x_28 = l_List_filterMapTR_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__10(x_27, x_26);
if (lean_obj_tag(x_28) == 1)
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_45; 
x_29 = lean_ctor_get(x_28, 0);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_28, 1);
lean_dec(x_46);
x_30 = x_28;
x_31 = x_45;
goto block_44;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_32 = lean_ctor_get(x_3, 0);
x_43 = !lean_is_exclusive(x_3);
if (x_43 == 0)
{
x_33 = x_3;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_dec(x_3);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; 
if (x_31 == 0)
{
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 0, x_32);
x_35 = x_30;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_29);
x_35 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_36; 
if (x_34 == 0)
{
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_35);
x_36 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_35);
x_36 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec_ref(x_3);
x_47 = lean_ctor_get(x_28, 0);
lean_inc(x_47);
lean_dec_ref(x_28);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
lean_dec(x_28);
x_50 = lean_ctor_get(x_1, 0);
x_51 = lean_ctor_get(x_1, 1);
x_52 = 0;
x_53 = l_Lean_Elab_Info_contains(x_3, x_50, x_52);
if (x_53 == 0)
{
x_9 = x_53;
goto block_25;
}
else
{
uint8_t x_54; 
x_54 = l_Lean_Elab_Info_contains(x_3, x_51, x_53);
x_9 = x_54;
goto block_25;
}
}
block_25:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_22; 
x_12 = lean_ctor_get(x_3, 0);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
x_13 = x_3;
x_14 = x_22;
goto block_21;
}
else
{
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_16);
x_17 = x_13;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_16);
x_17 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_3);
x_23 = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___closed__0));
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_38; 
x_5 = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15_spec__20___redArg___closed__0);
x_6 = l_ReaderT_instMonad___redArg(x_5);
x_7 = lean_ctor_get(x_6, 0);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_6, 1);
lean_dec(x_39);
x_8 = x_6;
x_9 = x_38;
goto block_37;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_35; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 2);
x_12 = lean_ctor_get(x_7, 3);
x_13 = lean_ctor_get(x_7, 4);
x_35 = !lean_is_exclusive(x_7);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_7, 1);
lean_dec(x_36);
x_14 = x_7;
x_15 = x_35;
goto block_34;
}
else
{
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__0));
x_17 = ((lean_object*)(l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___closed__1));
lean_inc_ref(x_10);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_10);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_12);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_23, 0, x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 4, x_21);
lean_ctor_set(x_14, 3, x_22);
lean_ctor_set(x_14, 2, x_23);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_20);
x_24 = x_14;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_20);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_22);
lean_ctor_set(x_33, 4, x_21);
x_24 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_25; 
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_24);
x_25 = x_8;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_17);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_box(0);
x_27 = l_instInhabitedOfMonad___redArg(x_25, x_26);
x_28 = lean_panic_fn(x_27, x_1);
x_29 = lean_apply_3(x_28, x_2, x_3, lean_box(0));
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_4);
x_10 = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(x_8, x_3);
x_3 = x_10;
x_4 = x_9;
goto _start;
}
case 1:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_12 = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__7_spec__15___redArg___closed__3);
x_13 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg(x_12, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_15);
lean_dec_ref(x_4);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_inc_ref(x_1);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
lean_inc_ref(x_14);
lean_inc(x_16);
x_17 = lean_apply_6(x_1, x_16, x_14, x_15, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; uint8_t x_44; 
lean_dec_ref(x_1);
x_44 = !lean_is_exclusive(x_3);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_3, 0);
lean_dec(x_45);
x_20 = x_3;
x_21 = x_44;
goto block_43;
}
else
{
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = lean_apply_7(x_2, x_16, x_14, x_15, x_22, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_34; 
x_24 = lean_ctor_get(x_23, 0);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
x_25 = x_23;
x_26 = x_34;
goto block_33;
}
else
{
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_box(0);
x_26 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_27; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_24);
x_27 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_24);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_26 == 0)
{
lean_ctor_set(x_25, 0, x_27);
x_28 = x_25;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_del_object(x_20);
x_35 = lean_ctor_get(x_23, 0);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
x_36 = x_23;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = l_Lean_Elab_Info_updateContext_x3f(x_3, x_14);
x_47 = l_Lean_PersistentArray_toList___redArg(x_15);
x_48 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_2);
x_49 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___redArg(x_1, x_2, x_46, x_47, x_48, x_5, x_6);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_apply_7(x_2, x_16, x_14, x_15, x_50, x_5, x_6, lean_box(0));
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_60; 
x_52 = lean_ctor_get(x_51, 0);
x_60 = !lean_is_exclusive(x_51);
if (x_60 == 0)
{
x_53 = x_51;
x_54 = x_60;
goto block_59;
}
else
{
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_box(0);
x_54 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_52);
if (x_54 == 0)
{
lean_ctor_set(x_53, 0, x_55);
x_56 = x_53;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_55);
x_56 = x_58;
goto block_57;
}
block_57:
{
return x_56;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
x_61 = lean_ctor_get(x_51, 0);
x_68 = !lean_is_exclusive(x_51);
if (x_68 == 0)
{
x_62 = x_51;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_51);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_76; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_69 = lean_ctor_get(x_49, 0);
x_76 = !lean_is_exclusive(x_49);
if (x_76 == 0)
{
x_70 = x_49;
x_71 = x_76;
goto block_75;
}
else
{
lean_inc(x_69);
lean_dec(x_49);
x_70 = lean_box(0);
x_71 = x_76;
goto block_75;
}
block_75:
{
lean_object* x_72; 
if (x_71 == 0)
{
x_72 = x_70;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_69);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_84; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_3);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_77 = lean_ctor_get(x_17, 0);
x_84 = !lean_is_exclusive(x_17);
if (x_84 == 0)
{
x_78 = x_17;
x_79 = x_84;
goto block_83;
}
else
{
lean_inc(x_77);
lean_dec(x_17);
x_78 = lean_box(0);
x_79 = x_84;
goto block_83;
}
block_83:
{
lean_object* x_80; 
if (x_79 == 0)
{
x_80 = x_78;
goto block_81;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_77);
x_80 = x_82;
goto block_81;
}
block_81:
{
return x_80;
}
}
}
}
}
default: 
{
lean_object* x_85; uint8_t x_86; uint8_t x_92; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_4);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_4, 0);
lean_dec(x_93);
x_85 = x_4;
x_86 = x_92;
goto block_91;
}
else
{
lean_dec(x_4);
x_85 = lean_box(0);
x_86 = x_92;
goto block_91;
}
block_91:
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_box(0);
if (x_86 == 0)
{
lean_ctor_set_tag(x_85, 0);
lean_ctor_set(x_85, 0, x_87);
x_88 = x_85;
goto block_89;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_87);
x_88 = x_90;
goto block_89;
}
block_89:
{
return x_88;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = l_List_reverse___redArg(x_5);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_30; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_30 = !lean_is_exclusive(x_4);
if (x_30 == 0)
{
x_13 = x_4;
x_14 = x_30;
goto block_29;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_15; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg(x_1, x_2, x_3, x_11, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (x_14 == 0)
{
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 0, x_16);
x_17 = x_13;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_5);
x_17 = x_20;
goto block_19;
}
block_19:
{
x_4 = x_12;
x_5 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_del_object(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_21 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_22 = x_15;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___lam__0___boxed), 8, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = ((lean_object*)(l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___closed__0));
x_8 = lean_box(0);
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg(x_7, x_6, x_8, x_2, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_33; 
x_7 = lean_ctor_get(x_6, 0);
x_33 = !lean_is_exclusive(x_6);
if (x_33 == 0)
{
x_8 = x_6;
x_9 = x_33;
goto block_32;
}
else
{
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = x_33;
goto block_32;
}
block_32:
{
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_31; 
x_15 = lean_ctor_get(x_7, 0);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
x_16 = x_7;
x_17 = x_31;
goto block_30;
}
else
{
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_31;
goto block_30;
}
block_30:
{
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_29; 
lean_del_object(x_8);
x_18 = lean_ctor_get(x_15, 0);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
x_19 = x_15;
x_20 = x_29;
goto block_28;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_List_reverse___redArg(x_18);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_21);
x_22 = x_19;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_21);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_17 == 0)
{
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_22);
x_23 = x_16;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_22);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_del_object(x_16);
lean_dec(x_15);
goto block_14;
}
}
}
else
{
lean_dec(x_7);
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
if (x_9 == 0)
{
lean_ctor_set(x_8, 0, x_10);
x_11 = x_8;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
x_34 = lean_ctor_get(x_6, 0);
x_41 = !lean_is_exclusive(x_6);
if (x_41 == 0)
{
x_35 = x_6;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13_spec__18(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_7, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget_borrowed(x_6, x_7);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_13);
lean_inc_ref(x_1);
x_14 = l_Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7(x_1, x_13, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_37; 
x_15 = lean_ctor_get(x_14, 0);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
x_16 = x_14;
x_17 = x_37;
goto block_36;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_37;
goto block_36;
}
block_36:
{
uint8_t x_18; uint8_t x_19; 
x_18 = 1;
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec_ref(x_15);
x_29 = lean_box(x_2);
lean_inc_ref(x_1);
x_30 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__0___boxed), 3, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_1);
x_31 = lean_box(x_2);
lean_inc_ref(x_1);
x_32 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1___boxed), 3, 2);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_1);
x_33 = lean_box(x_2);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_34 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__2___boxed), 7, 6);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_30);
lean_closure_set(x_34, 2, x_3);
lean_closure_set(x_34, 3, x_33);
lean_closure_set(x_34, 4, x_4);
lean_closure_set(x_34, 5, x_5);
x_35 = l_List_any___redArg(x_28, x_34);
x_19 = x_35;
goto block_27;
}
else
{
lean_dec(x_15);
x_19 = x_2;
goto block_27;
}
block_27:
{
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_del_object(x_16);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_23 = lean_box(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_14, 0);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
x_39 = x_14;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13_spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13_spec__18(x_1, x_12, x_3, x_4, x_5, x_6, x_13, x_14, x_9, x_10);
lean_dec_ref(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_7, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget_borrowed(x_6, x_7);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_13);
lean_inc_ref(x_1);
x_14 = l_Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7(x_1, x_13, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_37; 
x_15 = lean_ctor_get(x_14, 0);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
x_16 = x_14;
x_17 = x_37;
goto block_36;
}
else
{
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = x_37;
goto block_36;
}
block_36:
{
uint8_t x_18; uint8_t x_19; 
x_18 = 1;
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec_ref(x_15);
x_29 = lean_box(x_2);
lean_inc_ref(x_1);
x_30 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__0___boxed), 3, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_1);
x_31 = lean_box(x_2);
lean_inc_ref(x_1);
x_32 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1___boxed), 3, 2);
lean_closure_set(x_32, 0, x_31);
lean_closure_set(x_32, 1, x_1);
x_33 = lean_box(x_2);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_5);
x_34 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__2___boxed), 7, 6);
lean_closure_set(x_34, 0, x_32);
lean_closure_set(x_34, 1, x_30);
lean_closure_set(x_34, 2, x_5);
lean_closure_set(x_34, 3, x_33);
lean_closure_set(x_34, 4, x_3);
lean_closure_set(x_34, 5, x_4);
x_35 = l_List_any___redArg(x_28, x_34);
x_19 = x_35;
goto block_27;
}
else
{
lean_dec(x_15);
x_19 = x_2;
goto block_27;
}
block_27:
{
if (x_19 == 0)
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_del_object(x_16);
x_20 = 1;
x_21 = lean_usize_add(x_7, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13_spec__18(x_1, x_2, x_5, x_3, x_4, x_6, x_21, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_23 = lean_box(x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_23);
x_24 = x_16;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_45; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_38 = lean_ctor_get(x_14, 0);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
x_39 = x_14;
x_40 = x_45;
goto block_44;
}
else
{
lean_inc(x_38);
lean_dec(x_14);
x_39 = lean_box(0);
x_40 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_41; 
if (x_40 == 0)
{
x_41 = x_39;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_41 = x_43;
goto block_42;
}
block_42:
{
return x_41;
}
}
}
}
else
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_46 = 0;
x_47 = lean_box(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_15 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13(x_1, x_12, x_3, x_4, x_5, x_6, x_13, x_14, x_9, x_10);
lean_dec_ref(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_7 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_7 == 0)
{
x_3 = x_6;
goto _start;
}
else
{
lean_inc(x_5);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_instHashableFVarId_hash(x_2);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget_borrowed(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___redArg(x_2, x_3, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10_spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget_borrowed(x_3, x_4);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(x_1, x_7, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10_spec__14(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget_borrowed(x_3, x_4);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(x_1, x_7, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_12 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10_spec__14(x_1, x_2, x_3, x_11, x_5);
return x_12;
}
else
{
return x_9;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Syntax_hasArgs(x_3);
if (x_4 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8_spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(x_1, x_6, x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8_spec__10(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(x_1, x_6, x_6);
lean_dec(x_6);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8_spec__10(x_1, x_2, x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__11(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_11, x_10);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_164; 
x_23 = lean_array_uget(x_9, x_11);
x_24 = lean_ctor_get(x_23, 1);
x_25 = lean_ctor_get(x_23, 0);
x_164 = !lean_is_exclusive(x_23);
if (x_164 == 0)
{
x_26 = x_23;
x_27 = x_164;
goto block_163;
}
else
{
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_162; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_31);
lean_dec(x_24);
x_32 = lean_st_ref_get(x_2);
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
x_162 = !lean_is_exclusive(x_12);
if (x_162 == 0)
{
x_35 = x_12;
x_36 = x_162;
goto block_161;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_box(0);
x_36 = x_162;
goto block_161;
}
block_161:
{
uint8_t x_37; uint8_t x_47; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_70; uint8_t x_71; lean_object* x_102; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_156; uint8_t x_157; 
x_53 = lean_box(x_5);
x_54 = lean_box(x_1);
x_55 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___lam__0___boxed), 3, 2);
lean_closure_set(x_55, 0, x_53);
lean_closure_set(x_55, 1, x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1);
x_126 = lean_box(x_1);
lean_inc(x_25);
x_127 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1___boxed), 3, 2);
lean_closure_set(x_127, 0, x_126);
lean_closure_set(x_127, 1, x_25);
x_156 = lean_array_get_size(x_31);
x_157 = lean_nat_dec_lt(x_56, x_156);
if (x_157 == 0)
{
lean_dec(x_32);
x_128 = x_1;
goto block_155;
}
else
{
if (x_157 == 0)
{
lean_dec(x_32);
x_128 = x_1;
goto block_155;
}
else
{
size_t x_158; size_t x_159; uint8_t x_160; 
x_158 = 0;
x_159 = lean_usize_of_nat(x_156);
x_160 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10(x_7, x_32, x_31, x_158, x_159);
lean_dec(x_32);
x_128 = x_160;
goto block_155;
}
}
block_46:
{
lean_object* x_38; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_29);
x_38 = x_26;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_28);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_push(x_34, x_38);
x_40 = lean_box(x_37);
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_39);
lean_ctor_set(x_35, 0, x_40);
x_41 = x_35;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_39);
x_41 = x_43;
goto block_42;
}
block_42:
{
x_16 = x_41;
goto block_20;
}
}
}
block_50:
{
if (x_47 == 0)
{
x_37 = x_5;
goto block_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_del_object(x_35);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
x_48 = lean_box(x_5);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_34);
x_16 = x_49;
goto block_20;
}
}
block_52:
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_34);
x_16 = x_51;
goto block_20;
}
block_69:
{
size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_59 = lean_array_size(x_58);
x_60 = 0;
x_61 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8(x_7, x_59, x_60, x_58);
x_62 = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9(x_57, x_61);
lean_dec_ref(x_61);
x_63 = lean_st_ref_set(x_2, x_62);
x_64 = lean_st_ref_get(x_2);
x_65 = lean_array_get_size(x_31);
x_66 = lean_nat_dec_lt(x_56, x_65);
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec_ref(x_31);
x_47 = x_1;
goto block_50;
}
else
{
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec_ref(x_31);
x_47 = x_1;
goto block_50;
}
else
{
size_t x_67; uint8_t x_68; 
x_67 = lean_usize_of_nat(x_65);
x_68 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10(x_7, x_64, x_31, x_60, x_67);
lean_dec_ref(x_31);
lean_dec(x_64);
x_47 = x_68;
goto block_50;
}
}
}
block_101:
{
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec_ref(x_31);
x_72 = lean_unbox(x_33);
lean_dec(x_33);
x_37 = x_72;
goto block_46;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_33);
x_73 = lean_st_mk_ref(x_57);
lean_inc(x_2);
x_74 = l_Lean_Linter_UnusedVariables_visitAssignments(x_73, x_2, x_70);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec_ref(x_74);
x_75 = lean_st_ref_take(x_2);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_77);
lean_dec(x_75);
x_78 = lean_mk_empty_array_with_capacity(x_76);
lean_dec(x_76);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_lt(x_56, x_79);
if (x_80 == 0)
{
lean_dec_ref(x_77);
x_58 = x_78;
goto block_69;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_79, x_79);
if (x_81 == 0)
{
if (x_80 == 0)
{
lean_dec_ref(x_77);
x_58 = x_78;
goto block_69;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_79);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12(x_77, x_82, x_83, x_78);
lean_dec_ref(x_77);
x_58 = x_84;
goto block_69;
}
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_79);
x_87 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12(x_77, x_85, x_86, x_78);
lean_dec_ref(x_77);
x_58 = x_87;
goto block_69;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_100; 
lean_del_object(x_35);
lean_dec(x_34);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_14);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_88 = lean_ctor_get(x_74, 0);
x_100 = !lean_is_exclusive(x_74);
if (x_100 == 0)
{
x_89 = x_74;
x_90 = x_100;
goto block_99;
}
else
{
lean_inc(x_88);
lean_dec(x_74);
x_89 = lean_box(0);
x_90 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_13, 7);
lean_inc(x_91);
lean_dec_ref(x_13);
x_92 = lean_io_error_to_string(x_88);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_95);
x_96 = x_89;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_95);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
}
block_104:
{
uint8_t x_103; 
x_103 = lean_unbox(x_33);
if (x_103 == 0)
{
x_70 = x_102;
x_71 = x_5;
goto block_101;
}
else
{
x_70 = x_102;
x_71 = x_1;
goto block_101;
}
}
block_125:
{
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_array_get_size(x_6);
x_109 = lean_nat_dec_lt(x_56, x_108);
if (x_109 == 0)
{
lean_dec_ref(x_105);
lean_dec(x_25);
x_102 = x_106;
goto block_104;
}
else
{
if (x_109 == 0)
{
lean_dec_ref(x_105);
lean_dec(x_25);
x_102 = x_106;
goto block_104;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; 
x_110 = 0;
x_111 = lean_usize_of_nat(x_108);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_8);
lean_inc(x_29);
x_112 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13(x_25, x_1, x_29, x_105, x_8, x_6, x_110, x_111, x_13, x_14);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
x_102 = x_106;
goto block_104;
}
else
{
lean_object* x_115; 
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_33);
lean_ctor_set(x_115, 1, x_34);
x_16 = x_115;
goto block_20;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_del_object(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_116 = lean_ctor_get(x_112, 0);
x_123 = !lean_is_exclusive(x_112);
if (x_123 == 0)
{
x_117 = x_112;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
}
}
else
{
lean_object* x_124; 
lean_dec_ref(x_105);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_33);
lean_ctor_set(x_124, 1, x_34);
x_16 = x_124;
goto block_20;
}
}
block_155:
{
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_3, 0);
x_130 = lean_ctor_get(x_3, 4);
x_131 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg(x_129, x_25);
if (x_131 == 0)
{
lean_object* x_132; 
lean_inc(x_4);
x_132 = l_Lean_Syntax_findStack_x3f(x_4, x_127, x_55);
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg(x_30, x_14);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_Syntax_isIdent(x_136);
lean_dec(x_136);
if (x_139 == 0)
{
lean_dec(x_135);
x_105 = x_138;
x_106 = x_130;
x_107 = x_1;
goto block_125;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_array_get_size(x_8);
x_141 = lean_nat_dec_lt(x_56, x_140);
if (x_141 == 0)
{
lean_dec(x_135);
x_105 = x_138;
x_106 = x_130;
x_107 = x_1;
goto block_125;
}
else
{
if (x_141 == 0)
{
lean_dec(x_135);
x_105 = x_138;
x_106 = x_130;
x_107 = x_1;
goto block_125;
}
else
{
size_t x_142; size_t x_143; uint8_t x_144; 
x_142 = 0;
x_143 = lean_usize_of_nat(x_140);
lean_inc(x_138);
lean_inc(x_29);
x_144 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6(x_29, x_135, x_138, x_8, x_142, x_143);
x_105 = x_138;
x_106 = x_130;
x_107 = x_144;
goto block_125;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_152; 
lean_dec(x_136);
lean_dec(x_135);
lean_del_object(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_145 = lean_ctor_get(x_137, 0);
x_152 = !lean_is_exclusive(x_137);
if (x_152 == 0)
{
x_146 = x_137;
x_147 = x_152;
goto block_151;
}
else
{
lean_inc(x_145);
lean_dec(x_137);
x_146 = lean_box(0);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_147 == 0)
{
x_148 = x_146;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_145);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_dec(x_133);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
goto block_52;
}
}
else
{
lean_dec(x_132);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
goto block_52;
}
}
else
{
lean_object* x_153; 
lean_dec_ref(x_127);
lean_dec_ref(x_55);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_33);
lean_ctor_set(x_153, 1, x_34);
x_16 = x_153;
goto block_20;
}
}
else
{
lean_object* x_154; 
lean_dec_ref(x_127);
lean_dec_ref(x_55);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_33);
lean_ctor_set(x_154, 1, x_34);
x_16 = x_154;
goto block_20;
}
}
}
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_11, x_17);
x_11 = x_18;
x_12 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_1);
x_17 = lean_unbox(x_5);
x_18 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_19 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20(x_16, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_18, x_19, x_12, x_13, x_14);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, size_t x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_11, x_10);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_164; 
x_23 = lean_array_uget(x_9, x_11);
x_24 = lean_ctor_get(x_23, 1);
x_25 = lean_ctor_get(x_23, 0);
x_164 = !lean_is_exclusive(x_23);
if (x_164 == 0)
{
x_26 = x_23;
x_27 = x_164;
goto block_163;
}
else
{
lean_inc(x_24);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_162; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 2);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_24, 3);
lean_inc_ref(x_31);
lean_dec(x_24);
x_32 = lean_st_ref_get(x_2);
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 1);
x_162 = !lean_is_exclusive(x_12);
if (x_162 == 0)
{
x_35 = x_12;
x_36 = x_162;
goto block_161;
}
else
{
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_12);
x_35 = lean_box(0);
x_36 = x_162;
goto block_161;
}
block_161:
{
uint8_t x_37; uint8_t x_47; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_70; uint8_t x_71; lean_object* x_102; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_156; uint8_t x_157; 
x_53 = lean_box(x_6);
x_54 = lean_box(x_1);
x_55 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___lam__0___boxed), 3, 2);
lean_closure_set(x_55, 0, x_53);
lean_closure_set(x_55, 1, x_54);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20___closed__1);
x_126 = lean_box(x_1);
lean_inc(x_25);
x_127 = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13___lam__1___boxed), 3, 2);
lean_closure_set(x_127, 0, x_126);
lean_closure_set(x_127, 1, x_25);
x_156 = lean_array_get_size(x_31);
x_157 = lean_nat_dec_lt(x_56, x_156);
if (x_157 == 0)
{
lean_dec(x_32);
x_128 = x_1;
goto block_155;
}
else
{
if (x_157 == 0)
{
lean_dec(x_32);
x_128 = x_1;
goto block_155;
}
else
{
size_t x_158; size_t x_159; uint8_t x_160; 
x_158 = 0;
x_159 = lean_usize_of_nat(x_156);
x_160 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10(x_3, x_32, x_31, x_158, x_159);
lean_dec(x_32);
x_128 = x_160;
goto block_155;
}
}
block_46:
{
lean_object* x_38; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 1, x_28);
lean_ctor_set(x_26, 0, x_29);
x_38 = x_26;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_28);
x_38 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_array_push(x_34, x_38);
x_40 = lean_box(x_37);
if (x_36 == 0)
{
lean_ctor_set(x_35, 1, x_39);
lean_ctor_set(x_35, 0, x_40);
x_41 = x_35;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_39);
x_41 = x_43;
goto block_42;
}
block_42:
{
x_16 = x_41;
goto block_20;
}
}
}
block_50:
{
if (x_47 == 0)
{
x_37 = x_6;
goto block_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_del_object(x_35);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
x_48 = lean_box(x_6);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_34);
x_16 = x_49;
goto block_20;
}
}
block_52:
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_33);
lean_ctor_set(x_51, 1, x_34);
x_16 = x_51;
goto block_20;
}
block_69:
{
size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_59 = lean_array_size(x_58);
x_60 = 0;
x_61 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__8(x_3, x_59, x_60, x_58);
x_62 = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__9(x_57, x_61);
lean_dec_ref(x_61);
x_63 = lean_st_ref_set(x_2, x_62);
x_64 = lean_st_ref_get(x_2);
x_65 = lean_array_get_size(x_31);
x_66 = lean_nat_dec_lt(x_56, x_65);
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec_ref(x_31);
x_47 = x_1;
goto block_50;
}
else
{
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec_ref(x_31);
x_47 = x_1;
goto block_50;
}
else
{
size_t x_67; uint8_t x_68; 
x_67 = lean_usize_of_nat(x_65);
x_68 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__10(x_3, x_64, x_31, x_60, x_67);
lean_dec_ref(x_31);
lean_dec(x_64);
x_47 = x_68;
goto block_50;
}
}
}
block_101:
{
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec_ref(x_31);
x_72 = lean_unbox(x_33);
lean_dec(x_33);
x_37 = x_72;
goto block_46;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_33);
x_73 = lean_st_mk_ref(x_57);
lean_inc(x_2);
x_74 = l_Lean_Linter_UnusedVariables_visitAssignments(x_73, x_2, x_70);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec_ref(x_74);
x_75 = lean_st_ref_take(x_2);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc_ref(x_77);
lean_dec(x_75);
x_78 = lean_mk_empty_array_with_capacity(x_76);
lean_dec(x_76);
x_79 = lean_array_get_size(x_77);
x_80 = lean_nat_dec_lt(x_56, x_79);
if (x_80 == 0)
{
lean_dec_ref(x_77);
x_58 = x_78;
goto block_69;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_79, x_79);
if (x_81 == 0)
{
if (x_80 == 0)
{
lean_dec_ref(x_77);
x_58 = x_78;
goto block_69;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_79);
x_84 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12(x_77, x_82, x_83, x_78);
lean_dec_ref(x_77);
x_58 = x_84;
goto block_69;
}
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_79);
x_87 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__12(x_77, x_85, x_86, x_78);
lean_dec_ref(x_77);
x_58 = x_87;
goto block_69;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_100; 
lean_del_object(x_35);
lean_dec(x_34);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_14);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_88 = lean_ctor_get(x_74, 0);
x_100 = !lean_is_exclusive(x_74);
if (x_100 == 0)
{
x_89 = x_74;
x_90 = x_100;
goto block_99;
}
else
{
lean_inc(x_88);
lean_dec(x_74);
x_89 = lean_box(0);
x_90 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_13, 7);
lean_inc(x_91);
lean_dec_ref(x_13);
x_92 = lean_io_error_to_string(x_88);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
if (x_90 == 0)
{
lean_ctor_set(x_89, 0, x_95);
x_96 = x_89;
goto block_97;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_95);
x_96 = x_98;
goto block_97;
}
block_97:
{
return x_96;
}
}
}
}
}
block_104:
{
uint8_t x_103; 
x_103 = lean_unbox(x_33);
if (x_103 == 0)
{
x_70 = x_102;
x_71 = x_6;
goto block_101;
}
else
{
x_70 = x_102;
x_71 = x_1;
goto block_101;
}
}
block_125:
{
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_array_get_size(x_8);
x_109 = lean_nat_dec_lt(x_56, x_108);
if (x_109 == 0)
{
lean_dec_ref(x_105);
lean_dec(x_25);
x_102 = x_106;
goto block_104;
}
else
{
if (x_109 == 0)
{
lean_dec_ref(x_105);
lean_dec(x_25);
x_102 = x_106;
goto block_104;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; 
x_110 = 0;
x_111 = lean_usize_of_nat(x_108);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_7);
lean_inc(x_29);
x_112 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__13(x_25, x_1, x_29, x_105, x_7, x_8, x_110, x_111, x_13, x_14);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
x_102 = x_106;
goto block_104;
}
else
{
lean_object* x_115; 
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_33);
lean_ctor_set(x_115, 1, x_34);
x_16 = x_115;
goto block_20;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_del_object(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_116 = lean_ctor_get(x_112, 0);
x_123 = !lean_is_exclusive(x_112);
if (x_123 == 0)
{
x_117 = x_112;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_112);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
}
}
else
{
lean_object* x_124; 
lean_dec_ref(x_105);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_33);
lean_ctor_set(x_124, 1, x_34);
x_16 = x_124;
goto block_20;
}
}
block_155:
{
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_4, 0);
x_130 = lean_ctor_get(x_4, 4);
x_131 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg(x_129, x_25);
if (x_131 == 0)
{
lean_object* x_132; 
lean_inc(x_5);
x_132 = l_Lean_Syntax_findStack_x3f(x_5, x_127, x_55);
if (lean_obj_tag(x_132) == 1)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
if (lean_obj_tag(x_133) == 1)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec_ref(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg(x_30, x_14);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; uint8_t x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = l_Lean_Syntax_isIdent(x_136);
lean_dec(x_136);
if (x_139 == 0)
{
lean_dec(x_135);
x_105 = x_138;
x_106 = x_130;
x_107 = x_1;
goto block_125;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_array_get_size(x_7);
x_141 = lean_nat_dec_lt(x_56, x_140);
if (x_141 == 0)
{
lean_dec(x_135);
x_105 = x_138;
x_106 = x_130;
x_107 = x_1;
goto block_125;
}
else
{
if (x_141 == 0)
{
lean_dec(x_135);
x_105 = x_138;
x_106 = x_130;
x_107 = x_1;
goto block_125;
}
else
{
size_t x_142; size_t x_143; uint8_t x_144; 
x_142 = 0;
x_143 = lean_usize_of_nat(x_140);
lean_inc(x_138);
lean_inc(x_29);
x_144 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__6(x_29, x_135, x_138, x_7, x_142, x_143);
x_105 = x_138;
x_106 = x_130;
x_107 = x_144;
goto block_125;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_152; 
lean_dec(x_136);
lean_dec(x_135);
lean_del_object(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec_ref(x_31);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_145 = lean_ctor_get(x_137, 0);
x_152 = !lean_is_exclusive(x_137);
if (x_152 == 0)
{
x_146 = x_137;
x_147 = x_152;
goto block_151;
}
else
{
lean_inc(x_145);
lean_dec(x_137);
x_146 = lean_box(0);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_147 == 0)
{
x_148 = x_146;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_145);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
else
{
lean_dec(x_133);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
goto block_52;
}
}
else
{
lean_dec(x_132);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
goto block_52;
}
}
else
{
lean_object* x_153; 
lean_dec_ref(x_127);
lean_dec_ref(x_55);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_33);
lean_ctor_set(x_153, 1, x_34);
x_16 = x_153;
goto block_20;
}
}
else
{
lean_object* x_154; 
lean_dec_ref(x_127);
lean_dec_ref(x_55);
lean_del_object(x_35);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_del_object(x_26);
lean_dec(x_25);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_33);
lean_ctor_set(x_154, 1, x_34);
x_16 = x_154;
goto block_20;
}
}
}
}
}
block_20:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_11, x_17);
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14_spec__20(x_1, x_2, x_4, x_5, x_6, x_8, x_3, x_7, x_9, x_10, x_18, x_16, x_13, x_14);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_1);
x_17 = lean_unbox(x_6);
x_18 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_19 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14(x_16, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_18, x_19, x_12, x_13, x_14);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Command_instInhabitedScope_default;
x_7 = l_List_head_x21___redArg(x_6, x_5);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_Options_toLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__5___redArg(x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Linter_UnusedVariables_followAliases(x_7, x_5);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__6___redArg(x_2, x_4, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__22(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__23(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget_borrowed(x_2, x_3);
lean_inc(x_7);
x_8 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__22(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__23(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__18(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_array_push(x_1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__18___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__18(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__19(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
x_7 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__18(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__19(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__1));
x_5 = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Syntax_getPos_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_obj_once(&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3, &l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3);
x_16 = l_panic___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__2(x_15);
x_4 = x_16;
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec_ref(x_14);
x_4 = x_17;
goto block_12;
}
block_12:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Syntax_getPos_x3f(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_obj_once(&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3, &l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___closed__3);
x_8 = l_panic___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__2(x_7);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec_ref(x_6);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
lean_dec(x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0(x_4, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_box(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_7, 0, x_6);
lean_inc(x_3);
x_8 = l_Array_qpartition___redArg(x_2, x_7, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_nat_dec_le(x_4, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg(x_1, x_10, x_3, x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_9, x_13);
lean_dec(x_9);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
x_6 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Elab_Command_instInhabitedScope_default;
x_9 = l_List_head_x21___redArg(x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__2);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
lean_dec_ref(x_13);
x_14 = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__0_spec__0___closed__5);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_10);
x_16 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_1);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0___closed__0));
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
else
{
return x_1;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
x_5 = lean_unbox(x_2);
x_6 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_71; uint8_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; uint8_t x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_130; uint8_t x_143; 
x_125 = 2;
x_143 = l_Lean_instBEqMessageSeverity_beq(x_3, x_125);
if (x_143 == 0)
{
x_130 = x_143;
goto block_142;
}
else
{
uint8_t x_144; 
lean_inc_ref(x_2);
x_144 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_130 = x_144;
goto block_142;
}
block_70:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_Elab_Command_getScope___redArg(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_53; 
x_19 = lean_ctor_get(x_18, 0);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
x_20 = x_18;
x_21 = x_53;
goto block_52;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_51; 
x_22 = lean_st_ref_take(x_15);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_19, 3);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 2);
x_28 = lean_ctor_get(x_22, 3);
x_29 = lean_ctor_get(x_22, 4);
x_30 = lean_ctor_get(x_22, 5);
x_31 = lean_ctor_get(x_22, 6);
x_32 = lean_ctor_get(x_22, 7);
x_33 = lean_ctor_get(x_22, 8);
x_34 = lean_ctor_get(x_22, 9);
x_35 = lean_ctor_get(x_22, 10);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
x_36 = x_22;
x_37 = x_51;
goto block_50;
}
else
{
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_22);
x_36 = lean_box(0);
x_37 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_24);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_13);
x_40 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_8);
lean_ctor_set(x_40, 2, x_12);
lean_ctor_set(x_40, 3, x_14);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 1, x_10);
lean_ctor_set_uint8(x_40, sizeof(void*)*5 + 2, x_4);
x_41 = l_Lean_MessageLog_add(x_40, x_26);
if (x_37 == 0)
{
lean_ctor_set(x_36, 1, x_41);
x_42 = x_36;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_49, 0, x_25);
lean_ctor_set(x_49, 1, x_41);
lean_ctor_set(x_49, 2, x_27);
lean_ctor_set(x_49, 3, x_28);
lean_ctor_set(x_49, 4, x_29);
lean_ctor_set(x_49, 5, x_30);
lean_ctor_set(x_49, 6, x_31);
lean_ctor_set(x_49, 7, x_32);
lean_ctor_set(x_49, 8, x_33);
lean_ctor_set(x_49, 9, x_34);
lean_ctor_set(x_49, 10, x_35);
x_42 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_st_ref_set(x_15, x_42);
x_44 = lean_box(0);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_44);
x_45 = x_20;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
x_54 = lean_ctor_get(x_18, 0);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
x_55 = x_18;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_69; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_8);
x_62 = lean_ctor_get(x_16, 0);
x_69 = !lean_is_exclusive(x_16);
if (x_69 == 0)
{
x_63 = x_16;
x_64 = x_69;
goto block_68;
}
else
{
lean_inc(x_62);
lean_dec(x_16);
x_63 = lean_box(0);
x_64 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_65; 
if (x_64 == 0)
{
x_65 = x_63;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_62);
x_65 = x_67;
goto block_66;
}
block_66:
{
return x_65;
}
}
}
}
block_98:
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_97; 
x_76 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_77);
x_78 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
lean_dec_ref(x_5);
x_79 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(x_2);
x_80 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___redArg(x_79, x_6);
x_81 = lean_ctor_get(x_80, 0);
x_97 = !lean_is_exclusive(x_80);
if (x_97 == 0)
{
x_82 = x_80;
x_83 = x_97;
goto block_96;
}
else
{
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_box(0);
x_83 = x_97;
goto block_96;
}
block_96:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc_ref(x_77);
x_84 = l_Lean_FileMap_toPosition(x_77, x_74);
lean_dec(x_74);
x_85 = l_Lean_FileMap_toPosition(x_77, x_75);
lean_dec(x_75);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = ((lean_object*)(l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn___lam__2___closed__23_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_));
if (x_78 == 0)
{
lean_del_object(x_82);
x_8 = x_84;
x_9 = x_72;
x_10 = x_73;
x_11 = x_76;
x_12 = x_86;
x_13 = x_81;
x_14 = x_87;
x_15 = x_6;
goto block_70;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_box(x_71);
x_89 = lean_box(x_78);
x_90 = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___lam__0___boxed), 3, 2);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_89);
lean_inc(x_81);
x_91 = l_Lean_MessageData_hasTag(x_90, x_81);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_86);
lean_dec_ref(x_84);
lean_dec(x_81);
lean_dec_ref(x_76);
x_92 = lean_box(0);
if (x_83 == 0)
{
lean_ctor_set(x_82, 0, x_92);
x_93 = x_82;
goto block_94;
}
else
{
lean_object* x_95; 
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_93 = x_95;
goto block_94;
}
block_94:
{
return x_93;
}
}
else
{
lean_del_object(x_82);
x_8 = x_84;
x_9 = x_72;
x_10 = x_73;
x_11 = x_76;
x_12 = x_86;
x_13 = x_81;
x_14 = x_87;
x_15 = x_6;
goto block_70;
}
}
}
}
block_106:
{
lean_object* x_104; 
x_104 = l_Lean_Syntax_getTailPos_x3f(x_100, x_101);
lean_dec(x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_inc(x_103);
x_71 = x_99;
x_72 = x_101;
x_73 = x_102;
x_74 = x_103;
x_75 = x_103;
goto block_98;
}
else
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_71 = x_99;
x_72 = x_101;
x_73 = x_102;
x_74 = x_103;
x_75 = x_105;
goto block_98;
}
}
block_124:
{
lean_object* x_110; 
x_110 = l_Lean_Elab_Command_getRef___redArg(x_5);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = l_Lean_replaceRef(x_1, x_111);
lean_dec(x_111);
x_113 = l_Lean_Syntax_getPos_x3f(x_112, x_108);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_unsigned_to_nat(0u);
x_99 = x_107;
x_100 = x_112;
x_101 = x_108;
x_102 = x_109;
x_103 = x_114;
goto block_106;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
lean_dec_ref(x_113);
x_99 = x_107;
x_100 = x_112;
x_101 = x_108;
x_102 = x_109;
x_103 = x_115;
goto block_106;
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_116 = lean_ctor_get(x_110, 0);
x_123 = !lean_is_exclusive(x_110);
if (x_123 == 0)
{
x_117 = x_110;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
block_129:
{
if (x_128 == 0)
{
x_107 = x_126;
x_108 = x_127;
x_109 = x_3;
goto block_124;
}
else
{
x_107 = x_126;
x_108 = x_127;
x_109 = x_125;
goto block_124;
}
}
block_142:
{
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; 
x_131 = lean_st_ref_get(x_6);
x_132 = lean_ctor_get(x_131, 2);
lean_inc(x_132);
lean_dec(x_131);
x_133 = l_Lean_Elab_Command_instInhabitedScope_default;
x_134 = l_List_head_x21___redArg(x_133, x_132);
lean_dec(x_132);
x_135 = lean_ctor_get(x_134, 1);
lean_inc_ref(x_135);
lean_dec(x_134);
x_136 = 1;
x_137 = l_Lean_instBEqMessageSeverity_beq(x_3, x_136);
if (x_137 == 0)
{
lean_dec_ref(x_135);
x_126 = x_130;
x_127 = x_130;
x_128 = x_137;
goto block_129;
}
else
{
lean_object* x_138; uint8_t x_139; 
x_138 = l_Lean_warningAsError;
x_139 = l_Lean_Option_get___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_collectReferences_go_spec__0(x_135, x_138);
lean_dec_ref(x_135);
x_126 = x_130;
x_127 = x_130;
x_128 = x_139;
goto block_129;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
x_9 = lean_unbox(x_4);
x_10 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26(x_1, x_2, x_8, x_9, x_5, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = 0;
x_8 = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26(x_1, x_2, x_6, x_7, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_22; 
x_7 = lean_ctor_get(x_1, 0);
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_8 = x_1;
x_9 = x_22;
goto block_21;
}
else
{
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__1, &l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__1_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__1);
lean_inc(x_7);
x_11 = l_Lean_MessageData_ofName(x_7);
if (x_9 == 0)
{
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_11);
lean_ctor_set(x_8, 0, x_10);
x_12 = x_8;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_11);
x_12 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_obj_once(&l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__3, &l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__3_once, _init_l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___closed__3);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_MessageData_note(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22(x_2, x_17, x_4, x_5);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_29; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
x_13 = x_10;
x_14 = x_29;
goto block_28;
}
else
{
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Linter_linter_unusedVariables;
x_16 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___closed__1);
x_17 = l_Lean_MessageData_ofName(x_12);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_17);
lean_ctor_set(x_13, 0, x_16);
x_18 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_17);
x_18 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2__spec__4___redArg___closed__4);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_inc_ref(x_5);
x_21 = l_Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15(x_15, x_11, x_20, x_5, x_6);
lean_dec(x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec_ref(x_21);
x_22 = lean_box(0);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_3 = x_24;
x_4 = x_22;
goto _start;
}
else
{
lean_dec_ref(x_5);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0, &l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0_once, _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__2));
x_2 = lean_obj_once(&l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1, &l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1_once, _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_6; lean_object* x_7; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_180; 
x_20 = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__1(x_3, x_4);
x_21 = lean_ctor_get(x_20, 0);
x_180 = !lean_is_exclusive(x_20);
if (x_180 == 0)
{
x_22 = x_20;
x_23 = x_180;
goto block_179;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_180;
goto block_179;
}
block_19:
{
lean_object* x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_array_size(x_7);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__16(x_7, x_9, x_6, x_8, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_11 = x_10;
x_12 = x_17;
goto block_16;
}
else
{
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_8);
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_8);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
else
{
return x_10;
}
}
block_179:
{
uint8_t x_24; 
x_24 = l_Lean_Linter_getLinterUnusedVariables(x_21);
lean_dec(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_25);
x_26 = x_22;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_st_ref_get(x_4);
x_30 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_30);
lean_dec(x_29);
x_31 = l_Lean_MessageLog_hasErrors(x_30);
lean_dec_ref(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Lean_Syntax_getRange_x3f(x_2, x_31);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_170; 
x_33 = lean_ctor_get(x_32, 0);
x_170 = !lean_is_exclusive(x_32);
if (x_170 == 0)
{
x_34 = x_32;
x_35 = x_170;
goto block_169;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_170;
goto block_169;
}
block_169:
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; 
lean_inc(x_2);
x_36 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_hasSorry(x_2);
if (x_36 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_del_object(x_22);
x_49 = lean_st_ref_get(x_4);
x_50 = lean_st_ref_get(x_4);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_obj_once(&l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0, &l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0_once, _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__0);
x_53 = lean_obj_once(&l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1, &l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1_once, _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__1);
x_54 = ((lean_object*)(l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__2));
x_55 = lean_obj_once(&l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__3, &l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__3_once, _init_l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___closed__3);
x_56 = lean_st_mk_ref(x_55);
x_57 = lean_ctor_get(x_49, 8);
lean_inc_ref(x_57);
lean_dec(x_49);
x_58 = lean_ctor_get(x_57, 2);
lean_inc_ref(x_58);
lean_dec_ref(x_57);
x_59 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_59);
lean_dec(x_50);
x_60 = l_Lean_Linter_linterSetsExt;
x_61 = lean_ctor_get(x_60, 0);
lean_inc_ref(x_61);
x_62 = lean_ctor_get(x_61, 2);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = l_Lean_PersistentArray_toArray___redArg(x_58);
lean_dec_ref(x_58);
x_64 = lean_box(0);
x_65 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_1, x_60, x_59, x_62, x_64);
lean_dec(x_62);
lean_inc(x_56);
x_66 = l_Lean_Linter_UnusedVariables_collectReferences(x_63, x_33, x_65, x_56);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; uint8_t x_148; 
lean_del_object(x_34);
x_148 = !lean_is_exclusive(x_66);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_66, 0);
lean_dec(x_149);
x_67 = x_66;
x_68 = x_148;
goto block_147;
}
else
{
lean_dec(x_66);
x_67 = lean_box(0);
x_68 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_117; lean_object* x_118; lean_object* x_129; uint8_t x_132; 
x_69 = lean_st_ref_get(x_56);
lean_dec(x_56);
x_96 = lean_ctor_get(x_69, 1);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_69, 2);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_69, 3);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_96, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 1);
lean_inc_ref(x_100);
lean_dec_ref(x_96);
x_132 = lean_nat_dec_eq(x_99, x_51);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
lean_del_object(x_67);
x_133 = lean_ctor_get(x_98, 1);
lean_inc_ref(x_133);
lean_dec_ref(x_98);
x_134 = lean_array_get_size(x_133);
x_135 = lean_nat_dec_lt(x_51, x_134);
if (x_135 == 0)
{
lean_dec_ref(x_133);
x_117 = x_53;
x_118 = x_52;
goto block_128;
}
else
{
uint8_t x_136; 
x_136 = lean_nat_dec_le(x_134, x_134);
if (x_136 == 0)
{
if (x_135 == 0)
{
lean_dec_ref(x_133);
x_117 = x_53;
x_118 = x_52;
goto block_128;
}
else
{
size_t x_137; size_t x_138; lean_object* x_139; 
x_137 = 0;
x_138 = lean_usize_of_nat(x_134);
x_139 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__23(x_69, x_133, x_137, x_138, x_53);
lean_dec_ref(x_133);
x_129 = x_139;
goto block_131;
}
}
else
{
size_t x_140; size_t x_141; lean_object* x_142; 
x_140 = 0;
x_141 = lean_usize_of_nat(x_134);
x_142 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__23(x_69, x_133, x_140, x_141, x_53);
lean_dec_ref(x_133);
x_129 = x_142;
goto block_131;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec_ref(x_97);
lean_dec(x_69);
lean_dec_ref(x_63);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_143 = lean_box(0);
if (x_68 == 0)
{
lean_ctor_set(x_67, 0, x_143);
x_144 = x_67;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_143);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
block_95:
{
lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_75 = lean_box(x_36);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_array_size(x_74);
x_78 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_79 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__14(x_36, x_71, x_70, x_69, x_2, x_24, x_72, x_63, x_74, x_77, x_78, x_76, x_3, x_4);
lean_dec_ref(x_74);
lean_dec_ref(x_63);
lean_dec(x_69);
lean_dec_ref(x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_array_get_size(x_81);
x_83 = lean_nat_dec_eq(x_82, x_51);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_82, x_84);
x_86 = lean_nat_dec_le(x_51, x_85);
if (x_86 == 0)
{
lean_inc(x_85);
x_43 = x_85;
x_44 = x_81;
x_45 = x_78;
x_46 = x_85;
goto block_48;
}
else
{
x_43 = x_85;
x_44 = x_81;
x_45 = x_78;
x_46 = x_51;
goto block_48;
}
}
else
{
x_6 = x_78;
x_7 = x_81;
goto block_19;
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; uint8_t x_94; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_87 = lean_ctor_get(x_79, 0);
x_94 = !lean_is_exclusive(x_79);
if (x_94 == 0)
{
x_88 = x_79;
x_89 = x_94;
goto block_93;
}
else
{
lean_inc(x_87);
lean_dec(x_79);
x_88 = lean_box(0);
x_89 = x_94;
goto block_93;
}
block_93:
{
lean_object* x_90; 
if (x_89 == 0)
{
x_90 = x_88;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_87);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
block_116:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_st_mk_ref(x_102);
x_104 = l_Lean_Linter_getUnusedVariablesIgnoreFns___redArg(x_4);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = lean_mk_empty_array_with_capacity(x_99);
lean_dec(x_99);
x_107 = lean_array_get_size(x_100);
x_108 = lean_nat_dec_lt(x_51, x_107);
if (x_108 == 0)
{
lean_dec_ref(x_100);
x_70 = x_101;
x_71 = x_103;
x_72 = x_105;
x_73 = x_54;
x_74 = x_106;
goto block_95;
}
else
{
uint8_t x_109; 
x_109 = lean_nat_dec_le(x_107, x_107);
if (x_109 == 0)
{
if (x_108 == 0)
{
lean_dec_ref(x_100);
x_70 = x_101;
x_71 = x_103;
x_72 = x_105;
x_73 = x_54;
x_74 = x_106;
goto block_95;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; 
x_110 = 0;
x_111 = lean_usize_of_nat(x_107);
x_112 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__19(x_100, x_110, x_111, x_106);
lean_dec_ref(x_100);
x_70 = x_101;
x_71 = x_103;
x_72 = x_105;
x_73 = x_54;
x_74 = x_112;
goto block_95;
}
}
else
{
size_t x_113; size_t x_114; lean_object* x_115; 
x_113 = 0;
x_114 = lean_usize_of_nat(x_107);
x_115 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__19(x_100, x_113, x_114, x_106);
lean_dec_ref(x_100);
x_70 = x_101;
x_71 = x_103;
x_72 = x_105;
x_73 = x_54;
x_74 = x_115;
goto block_95;
}
}
}
block_128:
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_array_get_size(x_118);
x_120 = lean_nat_dec_lt(x_51, x_119);
if (x_120 == 0)
{
lean_dec_ref(x_118);
x_101 = x_117;
x_102 = x_97;
goto block_116;
}
else
{
uint8_t x_121; 
x_121 = lean_nat_dec_le(x_119, x_119);
if (x_121 == 0)
{
if (x_120 == 0)
{
lean_dec_ref(x_118);
x_101 = x_117;
x_102 = x_97;
goto block_116;
}
else
{
size_t x_122; size_t x_123; lean_object* x_124; 
x_122 = 0;
x_123 = lean_usize_of_nat(x_119);
x_124 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__21(x_118, x_122, x_123, x_97);
lean_dec_ref(x_118);
x_101 = x_117;
x_102 = x_124;
goto block_116;
}
}
else
{
size_t x_125; size_t x_126; lean_object* x_127; 
x_125 = 0;
x_126 = lean_usize_of_nat(x_119);
x_127 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__21(x_118, x_125, x_126, x_97);
lean_dec_ref(x_118);
x_101 = x_117;
x_102 = x_127;
goto block_116;
}
}
}
block_131:
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc_ref(x_130);
x_117 = x_129;
x_118 = x_130;
goto block_128;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_164; 
lean_dec_ref(x_63);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_2);
x_150 = lean_ctor_get(x_66, 0);
x_164 = !lean_is_exclusive(x_66);
if (x_164 == 0)
{
x_151 = x_66;
x_152 = x_164;
goto block_163;
}
else
{
lean_inc(x_150);
lean_dec(x_66);
x_151 = lean_box(0);
x_152 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_3, 7);
lean_inc(x_153);
lean_dec_ref(x_3);
x_154 = lean_io_error_to_string(x_150);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 3);
lean_ctor_set(x_34, 0, x_154);
x_155 = x_34;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_162, 0, x_154);
x_155 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = l_Lean_MessageData_ofFormat(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_156);
if (x_152 == 0)
{
lean_ctor_set(x_151, 0, x_157);
x_158 = x_151;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_157);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_del_object(x_34);
lean_dec(x_33);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_box(0);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_165);
x_166 = x_22;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_165);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
block_42:
{
lean_object* x_41; 
x_41 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg(x_36, x_38, x_37, x_40);
lean_dec(x_40);
x_6 = x_39;
x_7 = x_41;
goto block_19;
}
block_48:
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_46, x_43);
if (x_47 == 0)
{
lean_dec(x_43);
lean_inc(x_46);
x_37 = x_46;
x_38 = x_44;
x_39 = x_45;
x_40 = x_46;
goto block_42;
}
else
{
x_37 = x_46;
x_38 = x_44;
x_39 = x_45;
x_40 = x_43;
goto block_42;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_32);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_box(0);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_171);
x_172 = x_22;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_171);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_box(0);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_175);
x_176 = x_22;
goto block_177;
}
else
{
lean_object* x_178; 
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_175);
x_176 = x_178;
goto block_177;
}
block_177:
{
return x_176;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_UnusedVariables_unusedVariables___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Linter_UnusedVariables_unusedVariables___lam__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__4(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___redArg(x_1, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__17(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__3_spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__28(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__15_spec__22_spec__26_spec__37(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00__private_Lean_Linter_Util_0__Lean_Linter_collectMacroExpansions_x3f_go___at___00Lean_Linter_collectMacroExpansions_x3f___at___00Lean_Linter_UnusedVariables_unusedVariables_spec__7_spec__8_spec__11_spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_initFn_00___x40_Lean_Linter_UnusedVariables_1044370963____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Linter_UnusedVariables_unusedVariables));
x_3 = l_Lean_Elab_Command_addLinter(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_initFn_00___x40_Lean_Linter_UnusedVariables_1044370963____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_initFn_00___x40_Lean_Linter_UnusedVariables_1044370963____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isUnusedVariableWarning___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Linter_linter_unusedVariables;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_name_eq(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isUnusedVariableWarning___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_isUnusedVariableWarning___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isUnusedVariableWarning(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = ((lean_object*)(l_Lean_MessageData_isUnusedVariableWarning___closed__0));
x_3 = l_Lean_MessageData_hasTag(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isUnusedVariableWarning___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_isUnusedVariableWarning(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_UnusedVariables(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_745145867____hygCtx___hyg_4_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_unusedVariables = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_unusedVariables);
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_477737835____hygCtx___hyg_4_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_unusedVariables_funArgs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_unusedVariables_funArgs);
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_452823168____hygCtx___hyg_4_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_unusedVariables_patternVars = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_unusedVariables_patternVars);
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1654543230____hygCtx___hyg_4_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_unusedVariables_analyzeTactics = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_unusedVariables_analyzeTactics);
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3334728626____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_builtinUnusedVariablesIgnoreFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_builtinUnusedVariablesIgnoreFnsRef);
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_217797861____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_unusedVariablesIgnoreFnsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_unusedVariablesIgnoreFnsExt);
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1088826556____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3567963054____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1718240125____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_4137261419____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1582690914____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_1110682914____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2270162977____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_2349931167____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_3301546665____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_625197502____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_initFn_00___x40_Lean_Linter_UnusedVariables_727354328____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_UnusedVariables_0__Lean_Linter_UnusedVariables_initFn_00___x40_Lean_Linter_UnusedVariables_1044370963____hygCtx___hyg_2_()
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_UnusedVariables(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Linter_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_UnusedVariables(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_UnusedVariables(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_UnusedVariables(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_UnusedVariables(builtin);
}
#ifdef __cplusplus
}
#endif

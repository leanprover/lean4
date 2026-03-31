// Lean compiler output
// Module: Lean.Compiler.Options
// Imports: public import Lean.Util.Trace
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 143, 82, 28, 135, 162, 241, 93)}};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "type check code after each compiler step (this is useful for debugging purses)"};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 125, 149, 102, 13, 124, 121, 159)}};
static const lean_object* l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_check;
static const lean_string_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "traceUnnormalized"};
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 195, 182, 218, 120, 21, 244, 155)}};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "don't normalize declarations before tracing them at each pipeline step (this is useful for debugging purposes)"};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 122, 82, 37, 76, 180, 119, 208)}};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_traceUnnormalized;
static const lean_string_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "checkMeta"};
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 103, 13, 107, 90, 160, 27, 121)}};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 217, .m_capacity = 217, .m_length = 216, .m_data = "Check that `meta` declarations only refer to other `meta` declarations and ditto for non-`meta` declarations. Disabling this option may lead to delayed compiler errors and is\n    intended only for debugging purposes."};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 85, 206, 216, 132, 54, 116, 157)}};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_checkMeta;
static const lean_string_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "relaxedMetaCheck"};
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(226, 147, 114, 93, 159, 216, 105, 213)}};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "Allow mixed `meta`/non-`meta` references in the same module. References to imports are unaffected."};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 120, 132, 227, 161, 157, 88, 89)}};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
static const lean_string_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ignoreBorrowAnnotation"};
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 27, 225, 188, 250, 30, 246, 118)}};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "Ignore user defined borrow inference annotations. This is useful for export/extern forward declarations"};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(29, 100, 150, 147, 211, 120, 168, 13)}};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
static const lean_string_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "postponeCompile"};
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(171, 185, 42, 124, 107, 137, 69, 56)}};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Internal. Toggle experimental `leanir` separate compilation."};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(132, 149, 178, 155, 191, 156, 98, 153)}};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_postponeCompile;
static const lean_string_object l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inLeanIR"};
static const lean_object* l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 225, 22, 39, 99, 176, 182, 190)}};
static const lean_object* l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "Internal. Indicates whether the compiler is currently running in `leanir`."};
static const lean_object* l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 253, 116, 74, 206, 197, 253, 222)}};
static const lean_object* l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_inLeanIR;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_));
v___x_80_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_));
v___x_81_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_78_, v___x_79_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_));
v___x_100_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_));
v___x_101_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_));
v___x_102_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_99_, v___x_100_, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4____boxed(lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_120_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_));
v___x_121_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_));
v___x_122_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_));
v___x_123_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_120_, v___x_121_, v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4____boxed(lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_141_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_));
v___x_142_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_));
v___x_143_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_));
v___x_144_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_141_, v___x_142_, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4____boxed(lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_162_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_));
v___x_163_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_));
v___x_164_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_));
v___x_165_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_162_, v___x_163_, v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4____boxed(lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_183_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_));
v___x_184_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_));
v___x_185_ = ((lean_object*)(l_Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_));
v___x_186_ = l_Lean_Option_register___at___00Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_183_, v___x_184_, v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4____boxed(lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
return v_res_188_;
}
}
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_check = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_check);
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_traceUnnormalized = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_traceUnnormalized);
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_checkMeta = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_checkMeta);
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_relaxedMetaCheck = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_relaxedMetaCheck);
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_ignoreBorrowAnnotation = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_ignoreBorrowAnnotation);
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_postponeCompile = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_postponeCompile);
lean_dec_ref(res);
res = l_Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_inLeanIR = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_inLeanIR);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Options(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Options(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Options(builtin);
}
#ifdef __cplusplus
}
#endif

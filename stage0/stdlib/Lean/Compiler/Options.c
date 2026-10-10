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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "check"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 143, 82, 28, 135, 162, 241, 93)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "type check code after each compiler step (this is useful for debugging purses)"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 125, 149, 102, 13, 124, 121, 159)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_check;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "traceUnnormalized"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 195, 182, 218, 120, 21, 244, 155)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 111, .m_capacity = 111, .m_length = 110, .m_data = "don't normalize declarations before tracing them at each pipeline step (this is useful for debugging purposes)"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(206, 122, 82, 37, 76, 180, 119, 208)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_traceUnnormalized;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "checkMeta"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(84, 103, 13, 107, 90, 160, 27, 121)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 217, .m_capacity = 217, .m_length = 216, .m_data = "Check that `meta` declarations only refer to other `meta` declarations and ditto for non-`meta` declarations. Disabling this option may lead to delayed compiler errors and is\n    intended only for debugging purposes."};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(251, 85, 206, 216, 132, 54, 116, 157)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_checkMeta;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "relaxedMetaCheck"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(226, 147, 114, 93, 159, 216, 105, 213)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 99, .m_capacity = 99, .m_length = 98, .m_data = "Allow mixed `meta`/non-`meta` references in the same module. References to imports are unaffected."};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 120, 132, 227, 161, 157, 88, 89)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_relaxedMetaCheck;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ignoreBorrowAnnotation"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 27, 225, 188, 250, 30, 246, 118)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "Ignore user defined borrow inference annotations. This is useful for export/extern forward declarations"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(29, 100, 150, 147, 211, 120, 168, 13)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "postponeCompile"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(171, 185, 42, 124, 107, 137, 69, 56)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "Internal. Toggle experimental `leanir` separate compilation."};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(132, 149, 178, 155, 191, 156, 98, 153)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_postponeCompile;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "inLeanIR"};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 225, 22, 39, 99, 176, 182, 190)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "Internal. Indicates whether the compiler is currently running in `leanir`."};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(82, 228, 12, 51, 253, 162, 91, 128)}};
static const lean_ctor_object l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 253, 116, 74, 206, 197, 253, 222)}};
static const lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_compiler_inLeanIR;
lean_object* l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
return v_res_60_;
}
}
lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_));
v___x_78_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_));
v___x_80_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_77_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_81_;
v_res_81_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
return v_res_83_;
}
}
lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_));
v___x_101_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_));
v___x_102_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_));
v___x_103_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_100_, v___x_101_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_104_;
v_res_104_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4____boxed(lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
return v_res_106_;
}
}
lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_123_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_));
v___x_124_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_));
v___x_125_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_));
v___x_126_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_123_, v___x_124_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_127_;
v_res_127_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4____boxed(lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
return v_res_129_;
}
}
lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_146_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_));
v___x_147_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_));
v___x_148_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_));
v___x_149_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_146_, v___x_147_, v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_150_;
v_res_150_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
stack->m_obj
 = v_res_150_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4____boxed(lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
return v_res_152_;
}
}
lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_));
v___x_170_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_));
v___x_171_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_));
v___x_172_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_169_, v___x_170_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_173_;
v_res_173_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4____boxed(lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
return v_res_175_;
}
}
lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_));
v___x_193_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_));
v___x_194_ = ((lean_object*)(l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_));
v___x_195_ = l_Lean_Option_register___at___00__private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4__spec__0(v___x_192_, v___x_193_, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_196_;
v_res_196_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4____boxed(lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
return v_res_198_;
}
}
lean_object* runtime_initialize_Lean_Util_Trace(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_Trace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_1849413889____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_check = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_check);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3304370316____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_traceUnnormalized = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_traceUnnormalized);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3249429079____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_checkMeta = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_checkMeta);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_4218354360____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_relaxedMetaCheck = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_relaxedMetaCheck);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_17255182____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_ignoreBorrowAnnotation = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_ignoreBorrowAnnotation);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_222989792____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_compiler_postponeCompile = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_compiler_postponeCompile);
lean_dec_ref(res);
res = l___private_Lean_Compiler_Options_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_Options_3877235242____hygCtx___hyg_4_();
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

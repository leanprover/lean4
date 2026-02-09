// Lean compiler output
// Module: Lean.Util.PPExt
// Imports: public import Lean.Elab.InfoTree.Types import Init.Data.Format.Macro
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 218, 195, 175, 75, 103, 130, 245)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "(pretty printer) print raw expression/syntax tree"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 57, 50, 55, 239, 9, 191, 88)}};
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_raw;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showInfo"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 218, 195, 175, 75, 103, 130, 245)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 137, 0, 183, 224, 68, 248, 79)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "(pretty printer) print `SourceInfo` metadata with raw printer"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 57, 50, 55, 239, 9, 191, 88)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 108, 10, 35, 175, 118, 161, 63)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_raw_showInfo;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxDepth"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 218, 195, 175, 75, 103, 130, 245)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(111, 14, 85, 214, 194, 150, 182, 169)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "(pretty printer) maximum `Syntax` depth for raw printer"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 57, 50, 55, 239, 9, 191, 88)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(238, 112, 244, 26, 171, 180, 71, 58)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_raw_maxDepth;
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rawOnError"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(85, 114, 167, 44, 2, 128, 35, 118)}};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "(pretty printer) fallback to 'raw' printer when pretty printer fails"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
static lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 70, 198, 120, 184, 26, 75, 221)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_rawOnError;
LEAN_EXPORT lean_object* l_Lean_instCoeFormatFormatWithInfos___lam__0(lean_object*);
static const lean_closure_object l_Lean_instCoeFormatFormatWithInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instCoeFormatFormatWithInfos___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instCoeFormatFormatWithInfos___closed__0 = (const lean_object*)&l_Lean_instCoeFormatFormatWithInfos___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instCoeFormatFormatWithInfos = (const lean_object*)&l_Lean_instCoeFormatFormatWithInfos___closed__0_value;
static const lean_string_object l_Lean_instInhabitedPPFns_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lean_instInhabitedPPFns_default___lam__0___closed__0 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedPPFns_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lean_instInhabitedPPFns_default___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedPPFns_default___lam__0___closed__1 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedPPFns_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedPPFns_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedPPFns_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedPPFns_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedPPFns_default___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedPPFns_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedPPFns_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedPPFns_default___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedPPFns_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedPPFns_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedPPFns_default___lam__3___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedPPFns_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__3_value;
static const lean_closure_object l_Lean_instInhabitedPPFns_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedPPFns_default___lam__4___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedPPFns_default___closed__4 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__4_value;
static const lean_ctor_object l_Lean_instInhabitedPPFns_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedPPFns_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedPPFns_default___closed__1_value),((lean_object*)&l_Lean_instInhabitedPPFns_default___closed__2_value),((lean_object*)&l_Lean_instInhabitedPPFns_default___closed__3_value),((lean_object*)&l_Lean_instInhabitedPPFns_default___closed__4_value)}};
static const lean_object* l_Lean_instInhabitedPPFns_default___closed__5 = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedPPFns_default = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedPPFns = (const lean_object*)&l_Lean_instInhabitedPPFns_default___closed__5_value;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_formatRawTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_formatRawTerm___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_formatRawGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goal "};
static const lean_object* l_Lean_formatRawGoal___closed__0 = (const lean_object*)&l_Lean_formatRawGoal___closed__0_value;
static const lean_ctor_object l_Lean_formatRawGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_formatRawGoal___closed__0_value)}};
static const lean_object* l_Lean_formatRawGoal___closed__1 = (const lean_object*)&l_Lean_formatRawGoal___closed__1_value;
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_formatRawGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2__value;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppFnsRef;
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_;
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppExt;
static const lean_string_object l_Lean_ppExprWithInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 95, .m_capacity = 95, .m_length = 94, .m_data = "failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)"};
static const lean_object* l_Lean_ppExprWithInfos___closed__0 = (const lean_object*)&l_Lean_ppExprWithInfos___closed__0_value;
static const lean_ctor_object l_Lean_ppExprWithInfos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppExprWithInfos___closed__0_value)}};
static const lean_object* l_Lean_ppExprWithInfos___closed__1 = (const lean_object*)&l_Lean_ppExprWithInfos___closed__1_value;
static const lean_ctor_object l_Lean_ppExprWithInfos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ppExprWithInfos___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ppExprWithInfos___closed__2 = (const lean_object*)&l_Lean_ppExprWithInfos___closed__2_value;
static const lean_string_object l_Lean_ppExprWithInfos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "[Error pretty printing expression: "};
static const lean_object* l_Lean_ppExprWithInfos___closed__3 = (const lean_object*)&l_Lean_ppExprWithInfos___closed__3_value;
static const lean_ctor_object l_Lean_ppExprWithInfos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppExprWithInfos___closed__3_value)}};
static const lean_object* l_Lean_ppExprWithInfos___closed__4 = (const lean_object*)&l_Lean_ppExprWithInfos___closed__4_value;
static const lean_string_object l_Lean_ppExprWithInfos___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = ". Falling back to raw printer.]"};
static const lean_object* l_Lean_ppExprWithInfos___closed__5 = (const lean_object*)&l_Lean_ppExprWithInfos___closed__5_value;
static const lean_ctor_object l_Lean_ppExprWithInfos___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppExprWithInfos___closed__5_value)}};
static const lean_object* l_Lean_ppExprWithInfos___closed__6 = (const lean_object*)&l_Lean_ppExprWithInfos___closed__6_value;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ppConstNameWithInfos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "failed to pretty print constant (use 'set_option pp.rawOnError true' for raw representation)"};
static const lean_object* l_Lean_ppConstNameWithInfos___closed__0 = (const lean_object*)&l_Lean_ppConstNameWithInfos___closed__0_value;
static const lean_ctor_object l_Lean_ppConstNameWithInfos___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppConstNameWithInfos___closed__0_value)}};
static const lean_object* l_Lean_ppConstNameWithInfos___closed__1 = (const lean_object*)&l_Lean_ppConstNameWithInfos___closed__1_value;
static const lean_ctor_object l_Lean_ppConstNameWithInfos___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ppConstNameWithInfos___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ppConstNameWithInfos___closed__2 = (const lean_object*)&l_Lean_ppConstNameWithInfos___closed__2_value;
static const lean_string_object l_Lean_ppConstNameWithInfos___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "[Error pretty printing constant: "};
static const lean_object* l_Lean_ppConstNameWithInfos___closed__3 = (const lean_object*)&l_Lean_ppConstNameWithInfos___closed__3_value;
static const lean_ctor_object l_Lean_ppConstNameWithInfos___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppConstNameWithInfos___closed__3_value)}};
static const lean_object* l_Lean_ppConstNameWithInfos___closed__4 = (const lean_object*)&l_Lean_ppConstNameWithInfos___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ppTerm___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "failed to pretty print term (use 'set_option pp.rawOnError true' for raw representation)"};
static const lean_object* l_Lean_ppTerm___closed__0 = (const lean_object*)&l_Lean_ppTerm___closed__0_value;
static const lean_ctor_object l_Lean_ppTerm___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppTerm___closed__0_value)}};
static const lean_object* l_Lean_ppTerm___closed__1 = (const lean_object*)&l_Lean_ppTerm___closed__1_value;
static const lean_string_object l_Lean_ppTerm___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "[Error pretty printing syntax: "};
static const lean_object* l_Lean_ppTerm___closed__2 = (const lean_object*)&l_Lean_ppTerm___closed__2_value;
static const lean_ctor_object l_Lean_ppTerm___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppTerm___closed__2_value)}};
static const lean_object* l_Lean_ppTerm___closed__3 = (const lean_object*)&l_Lean_ppTerm___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_ppTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppTerm___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLevel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppLevel___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ppGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "failed to pretty print goal (use 'set_option pp.rawOnError true' for raw representation)"};
static const lean_object* l_Lean_ppGoal___closed__0 = (const lean_object*)&l_Lean_ppGoal___closed__0_value;
static const lean_ctor_object l_Lean_ppGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppGoal___closed__0_value)}};
static const lean_object* l_Lean_ppGoal___closed__1 = (const lean_object*)&l_Lean_ppGoal___closed__1_value;
static const lean_string_object l_Lean_ppGoal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "[Error pretty printing goal: "};
static const lean_object* l_Lean_ppGoal___closed__2 = (const lean_object*)&l_Lean_ppGoal___closed__2_value;
static const lean_ctor_object l_Lean_ppGoal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppGoal___closed__2_value)}};
static const lean_object* l_Lean_ppGoal___closed__3 = (const lean_object*)&l_Lean_ppGoal___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_ppGoal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppGoal___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_alloc_ctor(1, 0, 1);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, 0, x_9);
lean_inc(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_7);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_2);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 0, 1);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_20, 0, x_21);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_3);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_19);
lean_inc(x_1);
x_23 = lean_register_option(x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_24 = x_23;
} else {
 lean_dec_ref(x_23);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_18);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_1);
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_28 = x_23;
} else {
 lean_dec_ref(x_23);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_6);
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_17);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_3);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_18);
lean_inc(x_1);
x_21 = lean_register_option(x_1, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_22 = x_21;
} else {
 lean_dec_ref(x_21);
 x_22 = lean_box(0);
}
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_17);
if (lean_is_scalar(x_22)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_22;
}
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_1);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_26 = x_21;
} else {
 lean_dec_ref(x_21);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
x_3 = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
x_4 = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
x_3 = l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_;
x_4 = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
x_5 = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeFormatFormatWithInfos___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPPFns_default___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPPFns_default___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPPFns_default___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPPFns_default___lam__3(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instInhabitedPPFns_default___lam__4(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_dec(x_7);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 3);
x_4 = l_Lean_pp_raw_maxDepth;
x_5 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_pp_raw_showInfo;
x_8 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_3, x_7);
x_9 = l_Lean_Syntax_formatStx(x_2, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_formatRawTerm(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawGoal(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = ((lean_object*)(l_Lean_formatRawGoal___closed__1));
x_3 = l_Lean_mkMVar(x_1);
x_4 = lean_expr_dbg_to_string(x_3);
lean_dec_ref(x_3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_expr_dbg_to_string(x_2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = 1;
x_5 = l_Lean_Name_toString(x_2, x_4);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_formatRawTerm(x_1, x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l_Lean_Level_format(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_formatRawGoal(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(x_1, x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_));
x_3 = lean_st_mk_ref(x_2);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(x_1);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ppFnsRef;
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_;
x_3 = lean_box(0);
x_4 = lean_box(2);
x_5 = l_Lean_registerEnvExtension___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
x_7 = l_Lean_pp_raw;
x_8 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_ppExt;
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
x_11 = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
x_12 = lean_box(0);
lean_inc_ref(x_4);
x_13 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_11, x_9, x_4, x_10, x_12);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
lean_inc_ref(x_2);
x_15 = lean_apply_3(x_14, x_1, x_2, lean_box(0));
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = l_Lean_pp_rawOnError;
x_20 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_6, x_19);
lean_dec_ref(x_6);
if (x_20 == 0)
{
lean_object* x_21; 
lean_free_object(x_15);
lean_dec(x_18);
lean_dec_ref(x_2);
x_21 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__2));
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__4));
x_23 = lean_io_error_to_string(x_18);
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 0, x_23);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_15);
x_25 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_expr_dbg_to_string(x_2);
lean_dec_ref(x_2);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = l_Lean_pp_rawOnError;
x_36 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_6, x_35);
lean_dec_ref(x_6);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec_ref(x_2);
x_37 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__2));
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__4));
x_39 = lean_io_error_to_string(x_34);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_box(1);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_expr_dbg_to_string(x_2);
lean_dec_ref(x_2);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_box(1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec_ref(x_6);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_51 = l_Lean_instantiateMVarsCore(x_5, x_2);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_dec(x_54);
x_55 = lean_expr_dbg_to_string(x_53);
lean_dec(x_53);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_box(1);
lean_ctor_set(x_51, 1, x_57);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_expr_dbg_to_string(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ppExprWithInfos(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = l_Lean_ppExt;
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
x_9 = lean_box(0);
lean_inc_ref(x_4);
x_10 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_8, x_6, x_4, x_7, x_9);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec(x_10);
lean_inc(x_2);
x_12 = lean_apply_3(x_11, x_1, x_2, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_5);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_pp_rawOnError;
x_17 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_5, x_16);
lean_dec_ref(x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_2);
x_18 = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__2));
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__4));
x_20 = lean_io_error_to_string(x_15);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 0, x_20);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_12);
x_22 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Name_toString(x_2, x_17);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_12, 0);
lean_inc(x_31);
lean_dec(x_12);
x_32 = l_Lean_pp_rawOnError;
x_33 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_5, x_32);
lean_dec_ref(x_5);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_2);
x_34 = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__2));
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__4));
x_36 = lean_io_error_to_string(x_31);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(1);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Name_toString(x_2, x_33);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ppConstNameWithInfos(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ppTerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
x_6 = l_Lean_pp_raw;
x_7 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = l_Lean_ppExt;
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
x_10 = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
x_11 = lean_box(0);
lean_inc_ref(x_4);
x_12 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_10, x_8, x_4, x_9, x_11);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_13);
lean_dec(x_12);
lean_inc(x_2);
lean_inc_ref(x_1);
x_14 = lean_apply_3(x_13, x_1, x_2, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = l_Lean_pp_rawOnError;
x_19 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_5, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = ((lean_object*)(l_Lean_ppTerm___closed__1));
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = ((lean_object*)(l_Lean_ppTerm___closed__3));
x_22 = lean_io_error_to_string(x_17);
lean_ctor_set_tag(x_14, 3);
lean_ctor_set(x_14, 0, x_22);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_14);
x_24 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_formatRawTerm(x_1, x_2);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = l_Lean_pp_rawOnError;
x_32 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_5, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = ((lean_object*)(l_Lean_ppTerm___closed__1));
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = ((lean_object*)(l_Lean_ppTerm___closed__3));
x_35 = lean_io_error_to_string(x_30);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(1);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_formatRawTerm(x_1, x_2);
lean_dec_ref(x_1);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; 
x_44 = l_Lean_formatRawTerm(x_1, x_2);
lean_dec_ref(x_1);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppTerm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ppTerm(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_ppExt;
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
x_8 = lean_box(0);
lean_inc_ref(x_4);
x_9 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_7, x_5, x_4, x_6, x_8);
lean_dec(x_6);
x_10 = lean_ctor_get(x_9, 3);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_apply_3(x_10, x_1, x_2, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ppLevel(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_5);
x_6 = l_Lean_ppExt;
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
x_9 = lean_box(0);
lean_inc_ref(x_4);
x_10 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_8, x_6, x_4, x_7, x_9);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_11);
lean_dec(x_10);
lean_inc(x_2);
x_12 = lean_apply_3(x_11, x_1, x_2, lean_box(0));
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec_ref(x_5);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_Lean_pp_rawOnError;
x_17 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_5, x_16);
lean_dec_ref(x_5);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_12);
lean_dec(x_15);
lean_dec(x_2);
x_18 = ((lean_object*)(l_Lean_ppGoal___closed__1));
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = ((lean_object*)(l_Lean_ppGoal___closed__3));
x_20 = lean_io_error_to_string(x_15);
lean_ctor_set_tag(x_12, 3);
lean_ctor_set(x_12, 0, x_20);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_12);
x_22 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(1);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_formatRawGoal(x_2);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = l_Lean_pp_rawOnError;
x_30 = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(x_5, x_29);
lean_dec_ref(x_5);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_2);
x_31 = ((lean_object*)(l_Lean_ppGoal___closed__1));
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = ((lean_object*)(l_Lean_ppGoal___closed__3));
x_33 = lean_io_error_to_string(x_28);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(1);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_formatRawGoal(x_2);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ppGoal(x_1, x_2);
return x_4;
}
}
lean_object* initialize_Lean_Elab_InfoTree_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_PPExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw);
lean_dec_ref(res);
}l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_showInfo = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_showInfo);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_maxDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_maxDepth);
lean_dec_ref(res);
}l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = _init_l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
lean_mark_persistent(l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_rawOnError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_rawOnError);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ppFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppFnsRef);
lean_dec_ref(res);
}l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExt);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

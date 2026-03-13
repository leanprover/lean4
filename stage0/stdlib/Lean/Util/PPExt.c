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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 218, 195, 175, 75, 103, 130, 245)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "(pretty printer) print raw expression/syntax tree"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
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
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
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
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_formatRawTerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_formatRawTerm___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_formatRawGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "goal "};
static const lean_object* l_Lean_formatRawGoal___closed__0 = (const lean_object*)&l_Lean_formatRawGoal___closed__0_value;
static const lean_ctor_object l_Lean_formatRawGoal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_formatRawGoal___closed__0_value)}};
static const lean_object* l_Lean_formatRawGoal___closed__1 = (const lean_object*)&l_Lean_formatRawGoal___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_formatRawGoal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppFnsRef;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_;
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_58_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_55_, v___x_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_78_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_80_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_77_, v___x_78_, v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4____boxed(lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(lean_object* v_name_83_, lean_object* v_decl_84_, lean_object* v_ref_85_){
_start:
{
lean_object* v_defValue_87_; lean_object* v_descr_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_114_; 
v_defValue_87_ = lean_ctor_get(v_decl_84_, 0);
v_descr_88_ = lean_ctor_get(v_decl_84_, 1);
v_isSharedCheck_114_ = !lean_is_exclusive(v_decl_84_);
if (v_isSharedCheck_114_ == 0)
{
v___x_90_ = v_decl_84_;
v_isShared_91_ = v_isSharedCheck_114_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_descr_88_);
lean_inc(v_defValue_87_);
lean_dec(v_decl_84_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_114_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
lean_inc(v_defValue_87_);
v___x_92_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_92_, 0, v_defValue_87_);
lean_inc(v_name_83_);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v_name_83_);
lean_ctor_set(v___x_93_, 1, v_ref_85_);
lean_ctor_set(v___x_93_, 2, v___x_92_);
lean_ctor_set(v___x_93_, 3, v_descr_88_);
lean_inc(v_name_83_);
v___x_94_ = lean_register_option(v_name_83_, v___x_93_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_104_; 
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_94_, 0);
lean_dec(v_unused_105_);
v___x_96_ = v___x_94_;
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
else
{
lean_dec(v___x_94_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v_defValue_87_);
lean_ctor_set(v___x_90_, 0, v_name_83_);
v___x_99_ = v___x_90_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_name_83_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_defValue_87_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_101_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_99_);
v___x_101_ = v___x_96_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_99_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
}
else
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
lean_del_object(v___x_90_);
lean_dec(v_defValue_87_);
lean_dec(v_name_83_);
v_a_106_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_94_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_94_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_115_, lean_object* v_decl_116_, lean_object* v_ref_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v_name_115_, v_decl_116_, v_ref_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_136_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_137_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_138_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v___x_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4____boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_155_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_156_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_157_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_158_ = l_Lean_Option_register___at___00Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_155_, v___x_156_, v___x_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4____boxed(lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeFormatFormatWithInfos___lam__0(lean_object* v_fmt_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_box(1);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v_fmt_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0(lean_object* v_x_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0___boxed(lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_instInhabitedPPFns_default___lam__0(v_x_174_, v___y_175_);
lean_dec_ref(v___y_175_);
lean_dec_ref(v_x_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1(lean_object* v_x_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1___boxed(lean_object* v_x_183_, lean_object* v___y_184_, lean_object* v___y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_instInhabitedPPFns_default___lam__1(v_x_183_, v___y_184_);
lean_dec(v___y_184_);
lean_dec_ref(v_x_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2(lean_object* v_x_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2___boxed(lean_object* v_x_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_instInhabitedPPFns_default___lam__2(v_x_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v_x_192_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3(lean_object* v_x_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(0);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3___boxed(lean_object* v_x_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lean_instInhabitedPPFns_default___lam__3(v_x_200_, v___y_201_);
lean_dec(v___y_201_);
lean_dec_ref(v_x_200_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4(lean_object* v_x_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4___boxed(lean_object* v_x_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_instInhabitedPPFns_default___lam__4(v_x_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v_x_209_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(lean_object* v_opts_226_, lean_object* v_opt_227_){
_start:
{
lean_object* v_name_228_; lean_object* v_defValue_229_; lean_object* v_map_230_; lean_object* v___x_231_; 
v_name_228_ = lean_ctor_get(v_opt_227_, 0);
v_defValue_229_ = lean_ctor_get(v_opt_227_, 1);
v_map_230_ = lean_ctor_get(v_opts_226_, 0);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_230_, v_name_228_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_inc(v_defValue_229_);
return v_defValue_229_;
}
else
{
lean_object* v_val_232_; 
v_val_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_val_232_);
lean_dec_ref(v___x_231_);
if (lean_obj_tag(v_val_232_) == 3)
{
lean_object* v_v_233_; 
v_v_233_ = lean_ctor_get(v_val_232_, 0);
lean_inc(v_v_233_);
lean_dec_ref(v_val_232_);
return v_v_233_;
}
else
{
lean_dec(v_val_232_);
lean_inc(v_defValue_229_);
return v_defValue_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(lean_object* v_opts_234_, lean_object* v_opt_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_234_, v_opt_235_);
lean_dec_ref(v_opt_235_);
lean_dec_ref(v_opts_234_);
return v_res_236_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(lean_object* v_opts_237_, lean_object* v_opt_238_){
_start:
{
lean_object* v_name_239_; lean_object* v_defValue_240_; lean_object* v_map_241_; lean_object* v___x_242_; 
v_name_239_ = lean_ctor_get(v_opt_238_, 0);
v_defValue_240_ = lean_ctor_get(v_opt_238_, 1);
v_map_241_ = lean_ctor_get(v_opts_237_, 0);
v___x_242_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_241_, v_name_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
uint8_t v___x_243_; 
v___x_243_ = lean_unbox(v_defValue_240_);
return v___x_243_;
}
else
{
lean_object* v_val_244_; 
v_val_244_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_val_244_);
lean_dec_ref(v___x_242_);
if (lean_obj_tag(v_val_244_) == 1)
{
uint8_t v_v_245_; 
v_v_245_ = lean_ctor_get_uint8(v_val_244_, 0);
lean_dec_ref(v_val_244_);
return v_v_245_;
}
else
{
uint8_t v___x_246_; 
lean_dec(v_val_244_);
v___x_246_ = lean_unbox(v_defValue_240_);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(lean_object* v_opts_247_, lean_object* v_opt_248_){
_start:
{
uint8_t v_res_249_; lean_object* v_r_250_; 
v_res_249_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_247_, v_opt_248_);
lean_dec_ref(v_opt_248_);
lean_dec_ref(v_opts_247_);
v_r_250_ = lean_box(v_res_249_);
return v_r_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm(lean_object* v_ctx_251_, lean_object* v_stx_252_){
_start:
{
lean_object* v_opts_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v_opts_253_ = lean_ctor_get(v_ctx_251_, 3);
v___x_254_ = l_Lean_pp_raw_maxDepth;
v___x_255_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_253_, v___x_254_);
v___x_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
v___x_257_ = l_Lean_pp_raw_showInfo;
v___x_258_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_253_, v___x_257_);
v___x_259_ = l_Lean_Syntax_formatStx(v_stx_252_, v___x_256_, v___x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm___boxed(lean_object* v_ctx_260_, lean_object* v_stx_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_formatRawTerm(v_ctx_260_, v_stx_261_);
lean_dec_ref(v_ctx_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawGoal(lean_object* v_mvarId_266_){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_267_ = ((lean_object*)(l_Lean_formatRawGoal___closed__1));
v___x_268_ = l_Lean_mkMVar(v_mvarId_266_);
v___x_269_ = lean_expr_dbg_to_string(v___x_268_);
lean_dec_ref(v___x_268_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_267_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* v_x_272_, lean_object* v_e_273_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_275_ = lean_expr_dbg_to_string(v_e_273_);
v___x_276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = lean_box(1);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* v_x_280_, lean_object* v_e_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(v_x_280_, v_e_281_);
lean_dec_ref(v_e_281_);
lean_dec_ref(v_x_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* v_x_284_, lean_object* v_n_285_){
_start:
{
uint8_t v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = 1;
v___x_288_ = l_Lean_Name_toString(v_n_285_, v___x_287_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
v___x_290_ = lean_box(1);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* v_x_293_, lean_object* v_n_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(v_x_293_, v_n_294_);
lean_dec_ref(v_x_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* v_ctx_297_, lean_object* v_stx_298_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_Lean_formatRawTerm(v_ctx_297_, v_stx_298_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* v_ctx_302_, lean_object* v_stx_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(v_ctx_302_, v_stx_303_);
lean_dec_ref(v_ctx_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* v_x_306_, lean_object* v_l_307_){
_start:
{
uint8_t v___x_309_; lean_object* v___x_310_; 
v___x_309_ = 1;
v___x_310_ = l_Lean_Level_format(v_l_307_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* v_x_311_, lean_object* v_l_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(v_x_311_, v_l_312_);
lean_dec_ref(v_x_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(lean_object* v_x_315_, lean_object* v_mvarId_316_){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = l_Lean_formatRawGoal(v_mvarId_316_);
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* v_x_320_, lean_object* v_mvarId_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(v_x_320_, v_mvarId_321_);
lean_dec_ref(v_x_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_));
v___x_337_ = lean_st_mk_ref(v___x_336_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2____boxed(lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_();
return v_res_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object* v___x_341_){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_st_ref_get(v___x_341_);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v___x_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(v___x_345_);
lean_dec(v___x_345_);
return v_res_347_;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_348_; lean_object* v___f_349_; 
v___x_348_ = l_Lean_ppFnsRef;
v___f_349_ = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_349_, 0, v___x_348_);
return v___f_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___f_351_ = lean_obj_once(&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_, &l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_);
v___x_352_ = lean_box(0);
v___x_353_ = lean_box(2);
v___x_354_ = l_Lean_registerEnvExtension___redArg(v___f_351_, v___x_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos(lean_object* v_ctx_369_, lean_object* v_e_370_){
_start:
{
lean_object* v_env_372_; lean_object* v_mctx_373_; lean_object* v_opts_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_env_372_ = lean_ctor_get(v_ctx_369_, 0);
v_mctx_373_ = lean_ctor_get(v_ctx_369_, 1);
v_opts_374_ = lean_ctor_get(v_ctx_369_, 3);
lean_inc_ref(v_opts_374_);
v___x_375_ = l_Lean_pp_raw;
v___x_376_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; lean_object* v_asyncMode_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v_ppExprWithInfos_382_; lean_object* v___x_383_; 
v___x_377_ = l_Lean_ppExt;
v_asyncMode_378_ = lean_ctor_get(v___x_377_, 2);
lean_inc(v_asyncMode_378_);
v___x_379_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_380_ = lean_box(0);
lean_inc_ref(v_env_372_);
v___x_381_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_379_, v___x_377_, v_env_372_, v_asyncMode_378_, v___x_380_);
lean_dec(v_asyncMode_378_);
v_ppExprWithInfos_382_ = lean_ctor_get(v___x_381_, 0);
lean_inc_ref(v_ppExprWithInfos_382_);
lean_dec(v___x_381_);
lean_inc_ref(v_e_370_);
v___x_383_ = lean_apply_3(v_ppExprWithInfos_382_, v_ctx_369_, v_e_370_, lean_box(0));
if (lean_obj_tag(v___x_383_) == 0)
{
lean_object* v_a_384_; 
lean_dec_ref(v_opts_374_);
lean_dec_ref(v_e_370_);
v_a_384_ = lean_ctor_get(v___x_383_, 0);
lean_inc(v_a_384_);
lean_dec_ref(v___x_383_);
return v_a_384_;
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_407_; 
v_a_385_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_407_ == 0)
{
v___x_387_ = v___x_383_;
v_isShared_388_ = v_isSharedCheck_407_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_383_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_407_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = l_Lean_pp_rawOnError;
v___x_390_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_374_, v___x_389_);
lean_dec_ref(v_opts_374_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_del_object(v___x_387_);
lean_dec(v_a_385_);
lean_dec_ref(v_e_370_);
v___x_391_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__2));
return v___x_391_;
}
else
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_395_; 
v___x_392_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__4));
v___x_393_ = lean_io_error_to_string(v_a_385_);
if (v_isShared_388_ == 0)
{
lean_ctor_set_tag(v___x_387_, 3);
lean_ctor_set(v___x_387_, 0, v___x_393_);
v___x_395_ = v___x_387_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_406_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_396_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_392_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_box(1);
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_expr_dbg_to_string(v_e_370_);
lean_dec_ref(v_e_370_);
v___x_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_400_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_box(1);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
return v___x_405_;
}
}
}
}
}
else
{
lean_object* v___x_408_; lean_object* v_fst_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_419_; 
lean_inc_ref(v_mctx_373_);
lean_dec_ref(v_opts_374_);
lean_dec_ref(v_ctx_369_);
v___x_408_ = l_Lean_instantiateMVarsCore(v_mctx_373_, v_e_370_);
v_fst_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_408_, 1);
lean_dec(v_unused_420_);
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_fst_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_419_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_413_ = lean_expr_dbg_to_string(v_fst_409_);
lean_dec(v_fst_409_);
v___x_414_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
v___x_415_ = lean_box(1);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_415_);
lean_ctor_set(v___x_411_, 0, v___x_414_);
v___x_417_ = v___x_411_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos___boxed(lean_object* v_ctx_421_, lean_object* v_e_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_ppExprWithInfos(v_ctx_421_, v_e_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos(lean_object* v_ctx_434_, lean_object* v_n_435_){
_start:
{
lean_object* v_env_437_; lean_object* v_opts_438_; lean_object* v___x_439_; lean_object* v_asyncMode_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v_ppConstNameWithInfos_444_; lean_object* v___x_445_; 
v_env_437_ = lean_ctor_get(v_ctx_434_, 0);
v_opts_438_ = lean_ctor_get(v_ctx_434_, 3);
lean_inc_ref(v_opts_438_);
v___x_439_ = l_Lean_ppExt;
v_asyncMode_440_ = lean_ctor_get(v___x_439_, 2);
lean_inc(v_asyncMode_440_);
v___x_441_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_442_ = lean_box(0);
lean_inc_ref(v_env_437_);
v___x_443_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_441_, v___x_439_, v_env_437_, v_asyncMode_440_, v___x_442_);
lean_dec(v_asyncMode_440_);
v_ppConstNameWithInfos_444_ = lean_ctor_get(v___x_443_, 1);
lean_inc_ref(v_ppConstNameWithInfos_444_);
lean_dec(v___x_443_);
lean_inc(v_n_435_);
v___x_445_ = lean_apply_3(v_ppConstNameWithInfos_444_, v_ctx_434_, v_n_435_, lean_box(0));
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; 
lean_dec_ref(v_opts_438_);
lean_dec(v_n_435_);
v_a_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_a_446_);
lean_dec_ref(v___x_445_);
return v_a_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_469_; 
v_a_447_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_469_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_469_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_469_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = l_Lean_pp_rawOnError;
v___x_452_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_438_, v___x_451_);
lean_dec_ref(v_opts_438_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_del_object(v___x_449_);
lean_dec(v_a_447_);
lean_dec(v_n_435_);
v___x_453_ = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__2));
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_454_ = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__4));
v___x_455_ = lean_io_error_to_string(v_a_447_);
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 3);
lean_ctor_set(v___x_449_, 0, v___x_455_);
v___x_457_ = v___x_449_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_455_);
v___x_457_ = v_reuseFailAlloc_468_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_458_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_454_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
v___x_459_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_460_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_460_, 0, v___x_458_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
v___x_461_ = lean_box(1);
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_460_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = l_Lean_Name_toString(v_n_435_, v___x_452_);
v___x_464_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
v___x_465_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_462_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = lean_box(1);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_465_);
lean_ctor_set(v___x_467_, 1, v___x_466_);
return v___x_467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos___boxed(lean_object* v_ctx_470_, lean_object* v_n_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_ppConstNameWithInfos(v_ctx_470_, v_n_471_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppTerm(lean_object* v_ctx_480_, lean_object* v_stx_481_){
_start:
{
lean_object* v_env_483_; lean_object* v_opts_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_env_483_ = lean_ctor_get(v_ctx_480_, 0);
v_opts_484_ = lean_ctor_get(v_ctx_480_, 3);
v___x_485_ = l_Lean_pp_raw;
v___x_486_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v_asyncMode_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v_ppTerm_492_; lean_object* v___x_493_; 
v___x_487_ = l_Lean_ppExt;
v_asyncMode_488_ = lean_ctor_get(v___x_487_, 2);
lean_inc(v_asyncMode_488_);
v___x_489_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_490_ = lean_box(0);
lean_inc_ref(v_env_483_);
v___x_491_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_489_, v___x_487_, v_env_483_, v_asyncMode_488_, v___x_490_);
lean_dec(v_asyncMode_488_);
v_ppTerm_492_ = lean_ctor_get(v___x_491_, 2);
lean_inc_ref(v_ppTerm_492_);
lean_dec(v___x_491_);
lean_inc(v_stx_481_);
lean_inc_ref(v_ctx_480_);
v___x_493_ = lean_apply_3(v_ppTerm_492_, v_ctx_480_, v_stx_481_, lean_box(0));
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v_a_494_; 
lean_dec(v_stx_481_);
lean_dec_ref(v_ctx_480_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_a_494_);
lean_dec_ref(v___x_493_);
return v_a_494_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_514_; 
v_a_495_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_514_ == 0)
{
v___x_497_ = v___x_493_;
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = l_Lean_pp_rawOnError;
v___x_500_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_484_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_del_object(v___x_497_);
lean_dec(v_a_495_);
lean_dec(v_stx_481_);
lean_dec_ref(v_ctx_480_);
v___x_501_ = ((lean_object*)(l_Lean_ppTerm___closed__1));
return v___x_501_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_502_ = ((lean_object*)(l_Lean_ppTerm___closed__3));
v___x_503_ = lean_io_error_to_string(v_a_495_);
if (v_isShared_498_ == 0)
{
lean_ctor_set_tag(v___x_497_, 3);
lean_ctor_set(v___x_497_, 0, v___x_503_);
v___x_505_ = v___x_497_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_513_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_502_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_508_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_506_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v___x_509_ = lean_box(1);
v___x_510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_508_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = l_Lean_formatRawTerm(v_ctx_480_, v_stx_481_);
lean_dec_ref(v_ctx_480_);
v___x_512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
return v___x_512_;
}
}
}
}
}
else
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_formatRawTerm(v_ctx_480_, v_stx_481_);
lean_dec_ref(v_ctx_480_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppTerm___boxed(lean_object* v_ctx_516_, lean_object* v_stx_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_ppTerm(v_ctx_516_, v_stx_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLevel(lean_object* v_ctx_520_, lean_object* v_l_521_){
_start:
{
lean_object* v_env_523_; lean_object* v___x_524_; lean_object* v_asyncMode_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_ppLevel_529_; lean_object* v___x_530_; 
v_env_523_ = lean_ctor_get(v_ctx_520_, 0);
v___x_524_ = l_Lean_ppExt;
v_asyncMode_525_ = lean_ctor_get(v___x_524_, 2);
lean_inc(v_asyncMode_525_);
v___x_526_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_527_ = lean_box(0);
lean_inc_ref(v_env_523_);
v___x_528_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_526_, v___x_524_, v_env_523_, v_asyncMode_525_, v___x_527_);
lean_dec(v_asyncMode_525_);
v_ppLevel_529_ = lean_ctor_get(v___x_528_, 3);
lean_inc_ref(v_ppLevel_529_);
lean_dec(v___x_528_);
v___x_530_ = lean_apply_3(v_ppLevel_529_, v_ctx_520_, v_l_521_, lean_box(0));
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLevel___boxed(lean_object* v_ctx_531_, lean_object* v_l_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_ppLevel(v_ctx_531_, v_l_532_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal(lean_object* v_ctx_541_, lean_object* v_mvarId_542_){
_start:
{
lean_object* v_env_544_; lean_object* v_opts_545_; lean_object* v___x_546_; lean_object* v_asyncMode_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v_ppGoal_551_; lean_object* v___x_552_; 
v_env_544_ = lean_ctor_get(v_ctx_541_, 0);
v_opts_545_ = lean_ctor_get(v_ctx_541_, 3);
lean_inc_ref(v_opts_545_);
v___x_546_ = l_Lean_ppExt;
v_asyncMode_547_ = lean_ctor_get(v___x_546_, 2);
lean_inc(v_asyncMode_547_);
v___x_548_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_549_ = lean_box(0);
lean_inc_ref(v_env_544_);
v___x_550_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_548_, v___x_546_, v_env_544_, v_asyncMode_547_, v___x_549_);
lean_dec(v_asyncMode_547_);
v_ppGoal_551_ = lean_ctor_get(v___x_550_, 4);
lean_inc_ref(v_ppGoal_551_);
lean_dec(v___x_550_);
lean_inc(v_mvarId_542_);
v___x_552_ = lean_apply_3(v_ppGoal_551_, v_ctx_541_, v_mvarId_542_, lean_box(0));
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; 
lean_dec_ref(v_opts_545_);
lean_dec(v_mvarId_542_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref(v___x_552_);
return v_a_553_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_573_; 
v_a_554_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_573_ == 0)
{
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_573_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_573_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_558_ = l_Lean_pp_rawOnError;
v___x_559_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_545_, v___x_558_);
lean_dec_ref(v_opts_545_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; 
lean_del_object(v___x_556_);
lean_dec(v_a_554_);
lean_dec(v_mvarId_542_);
v___x_560_ = ((lean_object*)(l_Lean_ppGoal___closed__1));
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
v___x_561_ = ((lean_object*)(l_Lean_ppGoal___closed__3));
v___x_562_ = lean_io_error_to_string(v_a_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 3);
lean_ctor_set(v___x_556_, 0, v___x_562_);
v___x_564_ = v___x_556_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_562_);
v___x_564_ = v_reuseFailAlloc_572_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_561_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_567_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
v___x_568_ = lean_box(1);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_Lean_formatRawGoal(v_mvarId_542_);
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
return v___x_571_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal___boxed(lean_object* v_ctx_574_, lean_object* v_mvarId_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_ppGoal(v_ctx_574_, v_mvarId_575_);
return v_res_577_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_PPExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_showInfo = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_showInfo);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_maxDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_maxDepth);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_rawOnError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_rawOnError);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_PPExt_357215152____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ppFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppFnsRef);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ppExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_PPExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_Util_PPExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_PPExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_PPExt(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_mkMVar(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_MetavarContext_findLevelIndex_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value)}};
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_string_object l_Lean_ppLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "failed to pretty print level (use 'set_option pp.rawOnError true' for raw representation)"};
static const lean_object* l_Lean_ppLevel___closed__0 = (const lean_object*)&l_Lean_ppLevel___closed__0_value;
static const lean_ctor_object l_Lean_ppLevel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppLevel___closed__0_value)}};
static const lean_object* l_Lean_ppLevel___closed__1 = (const lean_object*)&l_Lean_ppLevel___closed__1_value;
static const lean_string_object l_Lean_ppLevel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "[Error pretty printing level: "};
static const lean_object* l_Lean_ppLevel___closed__2 = (const lean_object*)&l_Lean_ppLevel___closed__2_value;
static const lean_ctor_object l_Lean_ppLevel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_ppLevel___closed__2_value)}};
static const lean_object* l_Lean_ppLevel___closed__3 = (const lean_object*)&l_Lean_ppLevel___closed__3_value;
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
lean_inc_n(v_name_83_, 2);
v___x_93_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_93_, 0, v_name_83_);
lean_ctor_set(v___x_93_, 1, v_ref_85_);
lean_ctor_set(v___x_93_, 2, v___x_92_);
lean_ctor_set(v___x_93_, 3, v_descr_88_);
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
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3___boxed(lean_object* v_x_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_instInhabitedPPFns_default___lam__3(v_x_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v_x_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4(lean_object* v_x_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4___boxed(lean_object* v_x_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_instInhabitedPPFns_default___lam__4(v_x_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v_x_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(lean_object* v_opts_227_, lean_object* v_opt_228_){
_start:
{
lean_object* v_name_229_; lean_object* v_defValue_230_; lean_object* v_map_231_; lean_object* v___x_232_; 
v_name_229_ = lean_ctor_get(v_opt_228_, 0);
v_defValue_230_ = lean_ctor_get(v_opt_228_, 1);
v_map_231_ = lean_ctor_get(v_opts_227_, 0);
v___x_232_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_231_, v_name_229_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_inc(v_defValue_230_);
return v_defValue_230_;
}
else
{
lean_object* v_val_233_; 
v_val_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_233_);
lean_dec_ref(v___x_232_);
if (lean_obj_tag(v_val_233_) == 3)
{
lean_object* v_v_234_; 
v_v_234_ = lean_ctor_get(v_val_233_, 0);
lean_inc(v_v_234_);
lean_dec_ref(v_val_233_);
return v_v_234_;
}
else
{
lean_dec(v_val_233_);
lean_inc(v_defValue_230_);
return v_defValue_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(lean_object* v_opts_235_, lean_object* v_opt_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_235_, v_opt_236_);
lean_dec_ref(v_opt_236_);
lean_dec_ref(v_opts_235_);
return v_res_237_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(lean_object* v_opts_238_, lean_object* v_opt_239_){
_start:
{
lean_object* v_name_240_; lean_object* v_defValue_241_; lean_object* v_map_242_; lean_object* v___x_243_; 
v_name_240_ = lean_ctor_get(v_opt_239_, 0);
v_defValue_241_ = lean_ctor_get(v_opt_239_, 1);
v_map_242_ = lean_ctor_get(v_opts_238_, 0);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_242_, v_name_240_);
if (lean_obj_tag(v___x_243_) == 0)
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_defValue_241_);
return v___x_244_;
}
else
{
lean_object* v_val_245_; 
v_val_245_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_val_245_);
lean_dec_ref(v___x_243_);
if (lean_obj_tag(v_val_245_) == 1)
{
uint8_t v_v_246_; 
v_v_246_ = lean_ctor_get_uint8(v_val_245_, 0);
lean_dec_ref(v_val_245_);
return v_v_246_;
}
else
{
uint8_t v___x_247_; 
lean_dec(v_val_245_);
v___x_247_ = lean_unbox(v_defValue_241_);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(lean_object* v_opts_248_, lean_object* v_opt_249_){
_start:
{
uint8_t v_res_250_; lean_object* v_r_251_; 
v_res_250_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_248_, v_opt_249_);
lean_dec_ref(v_opt_249_);
lean_dec_ref(v_opts_248_);
v_r_251_ = lean_box(v_res_250_);
return v_r_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm(lean_object* v_ctx_252_, lean_object* v_stx_253_){
_start:
{
lean_object* v_opts_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; 
v_opts_254_ = lean_ctor_get(v_ctx_252_, 3);
v___x_255_ = l_Lean_pp_raw_maxDepth;
v___x_256_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_254_, v___x_255_);
v___x_257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
v___x_258_ = l_Lean_pp_raw_showInfo;
v___x_259_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_254_, v___x_258_);
v___x_260_ = l_Lean_Syntax_formatStx(v_stx_253_, v___x_257_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm___boxed(lean_object* v_ctx_261_, lean_object* v_stx_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_formatRawTerm(v_ctx_261_, v_stx_262_);
lean_dec_ref(v_ctx_261_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawGoal(lean_object* v_mvarId_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_268_ = ((lean_object*)(l_Lean_formatRawGoal___closed__1));
v___x_269_ = l_Lean_mkMVar(v_mvarId_267_);
v___x_270_ = lean_expr_dbg_to_string(v___x_269_);
lean_dec_ref(v___x_269_);
v___x_271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_268_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_273_, lean_object* v_e_274_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_276_ = lean_expr_dbg_to_string(v_e_274_);
v___x_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = lean_box(1);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_281_, lean_object* v_e_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_281_, v_e_282_);
lean_dec_ref(v_e_282_);
lean_dec_ref(v_x_281_);
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_285_, lean_object* v_n_286_){
_start:
{
uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_288_ = 1;
v___x_289_ = l_Lean_Name_toString(v_n_286_, v___x_288_);
v___x_290_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
v___x_291_ = lean_box(1);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_294_, lean_object* v_n_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_294_, v_n_295_);
lean_dec_ref(v_x_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_ctx_298_, lean_object* v_stx_299_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = l_Lean_formatRawTerm(v_ctx_298_, v_stx_299_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_ctx_303_, lean_object* v_stx_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_303_, v_stx_304_);
lean_dec_ref(v_ctx_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_ctx_307_, lean_object* v_l_308_){
_start:
{
lean_object* v_mctx_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_mctx_310_ = lean_ctor_get(v_ctx_307_, 1);
lean_inc_ref(v_mctx_310_);
lean_dec_ref(v_ctx_307_);
v___x_311_ = 1;
v___x_312_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_312_, 0, v_mctx_310_);
v___x_313_ = l_Lean_Level_format(v_l_308_, v___x_311_, v___x_312_);
v___x_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_ctx_315_, lean_object* v_l_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_315_, v_l_316_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_319_, lean_object* v_mvarId_320_){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = l_Lean_formatRawGoal(v_mvarId_320_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_324_, lean_object* v_mvarId_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_324_, v_mvarId_325_);
lean_dec_ref(v_x_324_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_));
v___x_341_ = lean_st_mk_ref(v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_a_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object* v___x_345_){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_st_ref_get(v___x_345_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v___x_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(v___x_349_);
lean_dec(v___x_349_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_352_; lean_object* v___f_353_; 
v___x_352_ = l_Lean_ppFnsRef;
v___f_353_ = lean_alloc_closure((void*)(l_Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_353_, 0, v___x_352_);
return v___f_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___f_355_ = lean_obj_once(&l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_, &l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_);
v___x_356_ = lean_box(0);
v___x_357_ = lean_box(2);
v___x_358_ = l_Lean_registerEnvExtension___redArg(v___f_355_, v___x_356_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos(lean_object* v_ctx_373_, lean_object* v_e_374_){
_start:
{
lean_object* v_env_376_; lean_object* v_mctx_377_; lean_object* v_opts_378_; lean_object* v___x_379_; uint8_t v___x_380_; 
v_env_376_ = lean_ctor_get(v_ctx_373_, 0);
v_mctx_377_ = lean_ctor_get(v_ctx_373_, 1);
v_opts_378_ = lean_ctor_get(v_ctx_373_, 3);
lean_inc_ref(v_opts_378_);
v___x_379_ = l_Lean_pp_raw;
v___x_380_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_378_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v_asyncMode_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v_ppExprWithInfos_386_; lean_object* v___x_387_; 
v___x_381_ = l_Lean_ppExt;
v_asyncMode_382_ = lean_ctor_get(v___x_381_, 2);
v___x_383_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_384_ = lean_box(0);
lean_inc_ref(v_env_376_);
v___x_385_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_383_, v___x_381_, v_env_376_, v_asyncMode_382_, v___x_384_);
v_ppExprWithInfos_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc_ref(v_ppExprWithInfos_386_);
lean_dec(v___x_385_);
lean_inc_ref(v_e_374_);
v___x_387_ = lean_apply_3(v_ppExprWithInfos_386_, v_ctx_373_, v_e_374_, lean_box(0));
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; 
lean_dec_ref(v_opts_378_);
lean_dec_ref(v_e_374_);
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc(v_a_388_);
lean_dec_ref(v___x_387_);
return v_a_388_;
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_411_; 
v_a_389_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_411_ == 0)
{
v___x_391_ = v___x_387_;
v_isShared_392_ = v_isSharedCheck_411_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_387_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_411_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = l_Lean_pp_rawOnError;
v___x_394_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_378_, v___x_393_);
lean_dec_ref(v_opts_378_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
lean_del_object(v___x_391_);
lean_dec(v_a_389_);
lean_dec_ref(v_e_374_);
v___x_395_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__2));
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_396_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__4));
v___x_397_ = lean_io_error_to_string(v_a_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 3);
lean_ctor_set(v___x_391_, 0, v___x_397_);
v___x_399_ = v___x_391_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_410_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_396_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_402_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_400_);
lean_ctor_set(v___x_402_, 1, v___x_401_);
v___x_403_ = lean_box(1);
v___x_404_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_402_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
v___x_405_ = lean_expr_dbg_to_string(v_e_374_);
lean_dec_ref(v_e_374_);
v___x_406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
v___x_407_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_404_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = lean_box(1);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
lean_ctor_set(v___x_409_, 1, v___x_408_);
return v___x_409_;
}
}
}
}
}
else
{
lean_object* v___x_412_; lean_object* v_fst_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_423_; 
lean_inc_ref(v_mctx_377_);
lean_dec_ref(v_opts_378_);
lean_dec_ref(v_ctx_373_);
v___x_412_ = l_Lean_instantiateMVarsCore(v_mctx_377_, v_e_374_);
v_fst_413_ = lean_ctor_get(v___x_412_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v___x_412_, 1);
lean_dec(v_unused_424_);
v___x_415_ = v___x_412_;
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_fst_413_);
lean_dec(v___x_412_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_423_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_417_ = lean_expr_dbg_to_string(v_fst_413_);
lean_dec(v_fst_413_);
v___x_418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = lean_box(1);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_419_);
lean_ctor_set(v___x_415_, 0, v___x_418_);
v___x_421_ = v___x_415_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos___boxed(lean_object* v_ctx_425_, lean_object* v_e_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_ppExprWithInfos(v_ctx_425_, v_e_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos(lean_object* v_ctx_438_, lean_object* v_n_439_){
_start:
{
lean_object* v_env_441_; lean_object* v_opts_442_; lean_object* v___x_443_; lean_object* v_asyncMode_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v_ppConstNameWithInfos_448_; lean_object* v___x_449_; 
v_env_441_ = lean_ctor_get(v_ctx_438_, 0);
v_opts_442_ = lean_ctor_get(v_ctx_438_, 3);
lean_inc_ref(v_opts_442_);
v___x_443_ = l_Lean_ppExt;
v_asyncMode_444_ = lean_ctor_get(v___x_443_, 2);
v___x_445_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_446_ = lean_box(0);
lean_inc_ref(v_env_441_);
v___x_447_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_445_, v___x_443_, v_env_441_, v_asyncMode_444_, v___x_446_);
v_ppConstNameWithInfos_448_ = lean_ctor_get(v___x_447_, 1);
lean_inc_ref(v_ppConstNameWithInfos_448_);
lean_dec(v___x_447_);
lean_inc(v_n_439_);
v___x_449_ = lean_apply_3(v_ppConstNameWithInfos_448_, v_ctx_438_, v_n_439_, lean_box(0));
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; 
lean_dec_ref(v_opts_442_);
lean_dec(v_n_439_);
v_a_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_a_450_);
lean_dec_ref(v___x_449_);
return v_a_450_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_473_; 
v_a_451_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_473_ == 0)
{
v___x_453_ = v___x_449_;
v_isShared_454_ = v_isSharedCheck_473_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_a_451_);
lean_dec(v___x_449_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_473_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = l_Lean_pp_rawOnError;
v___x_456_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_442_, v___x_455_);
lean_dec_ref(v_opts_442_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
lean_del_object(v___x_453_);
lean_dec(v_a_451_);
lean_dec(v_n_439_);
v___x_457_ = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__2));
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__4));
v___x_459_ = lean_io_error_to_string(v_a_451_);
if (v_isShared_454_ == 0)
{
lean_ctor_set_tag(v___x_453_, 3);
lean_ctor_set(v___x_453_, 0, v___x_459_);
v___x_461_ = v___x_453_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_472_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_462_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_458_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_464_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = lean_box(1);
v___x_466_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = l_Lean_Name_toString(v_n_439_, v___x_456_);
v___x_468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
v___x_469_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_466_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = lean_box(1);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_469_);
lean_ctor_set(v___x_471_, 1, v___x_470_);
return v___x_471_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos___boxed(lean_object* v_ctx_474_, lean_object* v_n_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_ppConstNameWithInfos(v_ctx_474_, v_n_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppTerm(lean_object* v_ctx_484_, lean_object* v_stx_485_){
_start:
{
lean_object* v_env_487_; lean_object* v_opts_488_; lean_object* v___x_489_; uint8_t v___x_490_; 
v_env_487_ = lean_ctor_get(v_ctx_484_, 0);
v_opts_488_ = lean_ctor_get(v_ctx_484_, 3);
v___x_489_ = l_Lean_pp_raw;
v___x_490_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_488_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v_asyncMode_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v_ppTerm_496_; lean_object* v___x_497_; 
v___x_491_ = l_Lean_ppExt;
v_asyncMode_492_ = lean_ctor_get(v___x_491_, 2);
v___x_493_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_494_ = lean_box(0);
lean_inc_ref(v_env_487_);
v___x_495_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_493_, v___x_491_, v_env_487_, v_asyncMode_492_, v___x_494_);
v_ppTerm_496_ = lean_ctor_get(v___x_495_, 2);
lean_inc_ref(v_ppTerm_496_);
lean_dec(v___x_495_);
lean_inc(v_stx_485_);
lean_inc_ref(v_ctx_484_);
v___x_497_ = lean_apply_3(v_ppTerm_496_, v_ctx_484_, v_stx_485_, lean_box(0));
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; 
lean_dec(v_stx_485_);
lean_dec_ref(v_ctx_484_);
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref(v___x_497_);
return v_a_498_;
}
else
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_518_; 
v_a_499_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_518_ == 0)
{
v___x_501_ = v___x_497_;
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_518_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; uint8_t v___x_504_; 
v___x_503_ = l_Lean_pp_rawOnError;
v___x_504_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_488_, v___x_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
lean_del_object(v___x_501_);
lean_dec(v_a_499_);
lean_dec(v_stx_485_);
lean_dec_ref(v_ctx_484_);
v___x_505_ = ((lean_object*)(l_Lean_ppTerm___closed__1));
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_506_ = ((lean_object*)(l_Lean_ppTerm___closed__3));
v___x_507_ = lean_io_error_to_string(v_a_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 3);
lean_ctor_set(v___x_501_, 0, v___x_507_);
v___x_509_ = v___x_501_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_507_);
v___x_509_ = v_reuseFailAlloc_517_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_506_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
v___x_511_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_512_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = lean_box(1);
v___x_514_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = l_Lean_formatRawTerm(v_ctx_484_, v_stx_485_);
lean_dec_ref(v_ctx_484_);
v___x_516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
return v___x_516_;
}
}
}
}
}
else
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_formatRawTerm(v_ctx_484_, v_stx_485_);
lean_dec_ref(v_ctx_484_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppTerm___boxed(lean_object* v_ctx_520_, lean_object* v_stx_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_ppTerm(v_ctx_520_, v_stx_521_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppLevel(lean_object* v_ctx_530_, lean_object* v_l_531_){
_start:
{
lean_object* v_env_533_; lean_object* v_mctx_534_; lean_object* v_opts_535_; lean_object* v___x_536_; lean_object* v_asyncMode_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v_ppLevel_541_; lean_object* v___x_542_; 
v_env_533_ = lean_ctor_get(v_ctx_530_, 0);
v_mctx_534_ = lean_ctor_get(v_ctx_530_, 1);
lean_inc_ref(v_mctx_534_);
v_opts_535_ = lean_ctor_get(v_ctx_530_, 3);
lean_inc_ref(v_opts_535_);
v___x_536_ = l_Lean_ppExt;
v_asyncMode_537_ = lean_ctor_get(v___x_536_, 2);
v___x_538_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_539_ = lean_box(0);
lean_inc_ref(v_env_533_);
v___x_540_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_538_, v___x_536_, v_env_533_, v_asyncMode_537_, v___x_539_);
v_ppLevel_541_ = lean_ctor_get(v___x_540_, 3);
lean_inc_ref(v_ppLevel_541_);
lean_dec(v___x_540_);
lean_inc(v_l_531_);
v___x_542_ = lean_apply_3(v_ppLevel_541_, v_ctx_530_, v_l_531_, lean_box(0));
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; 
lean_dec_ref(v_opts_535_);
lean_dec_ref(v_mctx_534_);
lean_dec(v_l_531_);
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v___x_542_);
return v_a_543_;
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_564_; 
v_a_544_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_564_ == 0)
{
v___x_546_ = v___x_542_;
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_542_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_564_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = l_Lean_pp_rawOnError;
v___x_549_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_535_, v___x_548_);
lean_dec_ref(v_opts_535_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_del_object(v___x_546_);
lean_dec(v_a_544_);
lean_dec_ref(v_mctx_534_);
lean_dec(v_l_531_);
v___x_550_ = ((lean_object*)(l_Lean_ppLevel___closed__1));
return v___x_550_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = ((lean_object*)(l_Lean_ppLevel___closed__3));
v___x_552_ = lean_io_error_to_string(v_a_544_);
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 3);
lean_ctor_set(v___x_546_, 0, v___x_552_);
v___x_554_ = v___x_546_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_552_);
v___x_554_ = v_reuseFailAlloc_563_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_551_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_555_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v___x_558_ = lean_box(1);
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_560_, 0, v_mctx_534_);
v___x_561_ = l_Lean_Level_format(v_l_531_, v___x_549_, v___x_560_);
v___x_562_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_559_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
return v___x_562_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppLevel___boxed(lean_object* v_ctx_565_, lean_object* v_l_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_ppLevel(v_ctx_565_, v_l_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal(lean_object* v_ctx_575_, lean_object* v_mvarId_576_){
_start:
{
lean_object* v_env_578_; lean_object* v_opts_579_; lean_object* v___x_580_; lean_object* v_asyncMode_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v_ppGoal_585_; lean_object* v___x_586_; 
v_env_578_ = lean_ctor_get(v_ctx_575_, 0);
v_opts_579_ = lean_ctor_get(v_ctx_575_, 3);
lean_inc_ref(v_opts_579_);
v___x_580_ = l_Lean_ppExt;
v_asyncMode_581_ = lean_ctor_get(v___x_580_, 2);
v___x_582_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_583_ = lean_box(0);
lean_inc_ref(v_env_578_);
v___x_584_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_582_, v___x_580_, v_env_578_, v_asyncMode_581_, v___x_583_);
v_ppGoal_585_ = lean_ctor_get(v___x_584_, 4);
lean_inc_ref(v_ppGoal_585_);
lean_dec(v___x_584_);
lean_inc(v_mvarId_576_);
v___x_586_ = lean_apply_3(v_ppGoal_585_, v_ctx_575_, v_mvarId_576_, lean_box(0));
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v_a_587_; 
lean_dec_ref(v_opts_579_);
lean_dec(v_mvarId_576_);
v_a_587_ = lean_ctor_get(v___x_586_, 0);
lean_inc(v_a_587_);
lean_dec_ref(v___x_586_);
return v_a_587_;
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_607_; 
v_a_588_ = lean_ctor_get(v___x_586_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_586_);
if (v_isSharedCheck_607_ == 0)
{
v___x_590_ = v___x_586_;
v_isShared_591_ = v_isSharedCheck_607_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_586_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_607_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = l_Lean_pp_rawOnError;
v___x_593_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_579_, v___x_592_);
lean_dec_ref(v_opts_579_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; 
lean_del_object(v___x_590_);
lean_dec(v_a_588_);
lean_dec(v_mvarId_576_);
v___x_594_ = ((lean_object*)(l_Lean_ppGoal___closed__1));
return v___x_594_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v___x_595_ = ((lean_object*)(l_Lean_ppGoal___closed__3));
v___x_596_ = lean_io_error_to_string(v_a_588_);
if (v_isShared_591_ == 0)
{
lean_ctor_set_tag(v___x_590_, 3);
lean_ctor_set(v___x_590_, 0, v___x_596_);
v___x_598_ = v___x_590_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_606_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_595_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_box(1);
v___x_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = l_Lean_formatRawGoal(v_mvarId_576_);
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal___boxed(lean_object* v_ctx_608_, lean_object* v_mvarId_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_ppGoal(v_ctx_608_, v_mvarId_609_);
return v_res_611_;
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
res = l_Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
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

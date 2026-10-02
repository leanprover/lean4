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
lean_object* l_Lean_MetavarContext_findLevelIndex_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_format(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "pp"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "raw"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 218, 195, 175, 75, 103, 130, 245)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "(pretty printer) print raw expression/syntax tree"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 57, 50, 55, 239, 9, 191, 88)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_raw;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "showInfo"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 218, 195, 175, 75, 103, 130, 245)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 137, 0, 183, 224, 68, 248, 79)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "(pretty printer) print `SourceInfo` metadata with raw printer"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 57, 50, 55, 239, 9, 191, 88)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 108, 10, 35, 175, 118, 161, 63)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_raw_showInfo;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxDepth"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 218, 195, 175, 75, 103, 130, 245)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(111, 14, 85, 214, 194, 150, 182, 169)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "(pretty printer) maximum `Syntax` depth for raw printer"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(143, 57, 50, 55, 239, 9, 191, 88)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(238, 112, 244, 26, 171, 180, 71, 58)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_pp_raw_maxDepth;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rawOnError"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(249, 51, 192, 169, 230, 180, 160, 93)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(85, 114, 167, 44, 2, 128, 35, 118)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "(pretty printer) fallback to 'raw' printer when pretty printer fails"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 7, 204, 203, 213, 214, 129, 229)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(48, 70, 198, 120, 184, 26, 75, 221)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppFnsRef;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_52_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_54_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_51_, v___x_52_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4____boxed(lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_76_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_77_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_74_, v___x_75_, v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4____boxed(lean_object* v_a_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(lean_object* v_name_80_, lean_object* v_decl_81_, lean_object* v_ref_82_){
_start:
{
lean_object* v_defValue_84_; lean_object* v_descr_85_; lean_object* v_deprecation_x3f_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_defValue_84_ = lean_ctor_get(v_decl_81_, 0);
v_descr_85_ = lean_ctor_get(v_decl_81_, 1);
v_deprecation_x3f_86_ = lean_ctor_get(v_decl_81_, 2);
lean_inc(v_defValue_84_);
v___x_87_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_87_, 0, v_defValue_84_);
lean_inc(v_deprecation_x3f_86_);
lean_inc_ref(v_descr_85_);
lean_inc_n(v_name_80_, 2);
v___x_88_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_88_, 0, v_name_80_);
lean_ctor_set(v___x_88_, 1, v_ref_82_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
lean_ctor_set(v___x_88_, 3, v_descr_85_);
lean_ctor_set(v___x_88_, 4, v_deprecation_x3f_86_);
v___x_89_ = lean_register_option(v_name_80_, v___x_88_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_97_ == 0)
{
lean_object* v_unused_98_; 
v_unused_98_ = lean_ctor_get(v___x_89_, 0);
lean_dec(v_unused_98_);
v___x_91_ = v___x_89_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_dec(v___x_89_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
lean_inc(v_defValue_84_);
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_name_80_);
lean_ctor_set(v___x_93_, 1, v_defValue_84_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v_a_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_106_; 
lean_dec(v_name_80_);
v_a_99_ = lean_ctor_get(v___x_89_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_106_ == 0)
{
v___x_101_ = v___x_89_;
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_a_99_);
lean_dec(v___x_89_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_106_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_104_; 
if (v_isShared_102_ == 0)
{
v___x_104_ = v___x_101_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_a_99_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_107_, lean_object* v_decl_108_, lean_object* v_ref_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v_name_107_, v_decl_108_, v_ref_109_);
lean_dec_ref(v_decl_108_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_129_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_130_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_131_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v___x_128_, v___x_129_, v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4____boxed(lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_150_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_151_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_152_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_149_, v___x_150_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4____boxed(lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_instCoeFormatFormatWithInfos___lam__0(lean_object* v_fmt_155_){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_box(1);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_fmt_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0(lean_object* v_x_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0___boxed(lean_object* v_x_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_instInhabitedPPFns_default___lam__0(v_x_168_, v___y_169_);
lean_dec_ref(v___y_169_);
lean_dec_ref(v_x_168_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1(lean_object* v_x_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1___boxed(lean_object* v_x_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_instInhabitedPPFns_default___lam__1(v_x_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v_x_177_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2(lean_object* v_x_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2___boxed(lean_object* v_x_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_instInhabitedPPFns_default___lam__2(v_x_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v_x_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3(lean_object* v_x_190_, lean_object* v___y_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3___boxed(lean_object* v_x_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_instInhabitedPPFns_default___lam__3(v_x_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v_x_195_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4(lean_object* v_x_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4___boxed(lean_object* v_x_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_instInhabitedPPFns_default___lam__4(v_x_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v_x_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(lean_object* v_opts_221_, lean_object* v_opt_222_){
_start:
{
lean_object* v_name_223_; lean_object* v_defValue_224_; lean_object* v_map_225_; lean_object* v___x_226_; 
v_name_223_ = lean_ctor_get(v_opt_222_, 0);
v_defValue_224_ = lean_ctor_get(v_opt_222_, 1);
v_map_225_ = lean_ctor_get(v_opts_221_, 0);
v___x_226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_225_, v_name_223_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_inc(v_defValue_224_);
return v_defValue_224_;
}
else
{
lean_object* v_val_227_; 
v_val_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_val_227_);
lean_dec_ref_known(v___x_226_, 1);
if (lean_obj_tag(v_val_227_) == 3)
{
lean_object* v_v_228_; 
v_v_228_ = lean_ctor_get(v_val_227_, 0);
lean_inc(v_v_228_);
lean_dec_ref_known(v_val_227_, 1);
return v_v_228_;
}
else
{
lean_dec(v_val_227_);
lean_inc(v_defValue_224_);
return v_defValue_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(lean_object* v_opts_229_, lean_object* v_opt_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_229_, v_opt_230_);
lean_dec_ref(v_opt_230_);
lean_dec_ref(v_opts_229_);
return v_res_231_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(lean_object* v_opts_232_, lean_object* v_opt_233_){
_start:
{
lean_object* v_name_234_; lean_object* v_defValue_235_; lean_object* v_map_236_; lean_object* v___x_237_; 
v_name_234_ = lean_ctor_get(v_opt_233_, 0);
v_defValue_235_ = lean_ctor_get(v_opt_233_, 1);
v_map_236_ = lean_ctor_get(v_opts_232_, 0);
v___x_237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_236_, v_name_234_);
if (lean_obj_tag(v___x_237_) == 0)
{
uint8_t v___x_238_; 
v___x_238_ = lean_unbox(v_defValue_235_);
return v___x_238_;
}
else
{
lean_object* v_val_239_; 
v_val_239_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_val_239_);
lean_dec_ref_known(v___x_237_, 1);
if (lean_obj_tag(v_val_239_) == 1)
{
uint8_t v_v_240_; 
v_v_240_ = lean_ctor_get_uint8(v_val_239_, 0);
lean_dec_ref_known(v_val_239_, 0);
return v_v_240_;
}
else
{
uint8_t v___x_241_; 
lean_dec(v_val_239_);
v___x_241_ = lean_unbox(v_defValue_235_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(lean_object* v_opts_242_, lean_object* v_opt_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_242_, v_opt_243_);
lean_dec_ref(v_opt_243_);
lean_dec_ref(v_opts_242_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm(lean_object* v_ctx_246_, lean_object* v_stx_247_){
_start:
{
lean_object* v_opts_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; 
v_opts_248_ = lean_ctor_get(v_ctx_246_, 3);
v___x_249_ = l_Lean_pp_raw_maxDepth;
v___x_250_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_248_, v___x_249_);
v___x_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
v___x_252_ = l_Lean_pp_raw_showInfo;
v___x_253_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_248_, v___x_252_);
v___x_254_ = l_Lean_Syntax_formatStx(v_stx_247_, v___x_251_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm___boxed(lean_object* v_ctx_255_, lean_object* v_stx_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_formatRawTerm(v_ctx_255_, v_stx_256_);
lean_dec_ref(v_ctx_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawGoal(lean_object* v_mvarId_261_){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(l_Lean_formatRawGoal___closed__1));
v___x_263_ = l_Lean_mkMVar(v_mvarId_261_);
v___x_264_ = lean_expr_dbg_to_string(v___x_263_);
lean_dec_ref(v___x_263_);
v___x_265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
v___x_266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_262_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_267_, lean_object* v_e_268_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_270_ = lean_expr_dbg_to_string(v_e_268_);
v___x_271_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
v___x_272_ = lean_box(1);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_275_, lean_object* v_e_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_275_, v_e_276_);
lean_dec_ref(v_e_276_);
lean_dec_ref(v_x_275_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_279_, lean_object* v_n_280_){
_start:
{
uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_282_ = 1;
v___x_283_ = l_Lean_Name_toString(v_n_280_, v___x_282_);
v___x_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
v___x_285_ = lean_box(1);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_288_, lean_object* v_n_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_288_, v_n_289_);
lean_dec_ref(v_x_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_ctx_292_, lean_object* v_stx_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = l_Lean_formatRawTerm(v_ctx_292_, v_stx_293_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_ctx_297_, lean_object* v_stx_298_, lean_object* v___y_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_297_, v_stx_298_);
lean_dec_ref(v_ctx_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_ctx_301_, lean_object* v_l_302_){
_start:
{
lean_object* v_mctx_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_mctx_304_ = lean_ctor_get(v_ctx_301_, 1);
lean_inc_ref(v_mctx_304_);
lean_dec_ref(v_ctx_301_);
v___x_305_ = 1;
v___x_306_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_306_, 0, v_mctx_304_);
v___x_307_ = l_Lean_Level_format(v_l_302_, v___x_305_, v___x_306_);
v___x_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_ctx_309_, lean_object* v_l_310_, lean_object* v___y_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_309_, v_l_310_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_313_, lean_object* v_mvarId_314_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = l_Lean_formatRawGoal(v_mvarId_314_);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_318_, lean_object* v_mvarId_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_318_, v_mvarId_319_);
lean_dec_ref(v_x_318_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_));
v___x_335_ = lean_st_mk_ref(v___x_334_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object* v___x_339_){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_st_ref_get(v___x_339_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v___x_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(v___x_343_);
lean_dec(v___x_343_);
return v_res_345_;
}
}
static lean_object* _init_l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_346_; lean_object* v___f_347_; 
v___x_346_ = l_Lean_ppFnsRef;
v___f_347_ = lean_alloc_closure((void*)(l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_347_, 0, v___x_346_);
return v___f_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; lean_object* v___x_354_; 
v___f_349_ = lean_obj_once(&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_, &l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once, _init_l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_);
v___x_350_ = lean_box(0);
v___x_351_ = lean_box(2);
v___x_352_ = lean_box(0);
v___x_353_ = 0;
v___x_354_ = l_Lean_registerEnvExtension___redArg(v___f_349_, v___x_350_, v___x_351_, v___x_352_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
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
v___x_379_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_380_ = lean_box(0);
lean_inc_ref(v_env_372_);
v___x_381_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_379_, v___x_377_, v_env_372_, v_asyncMode_378_, v___x_380_);
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
lean_dec_ref_known(v___x_383_, 1);
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
v___x_441_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_442_ = lean_box(0);
lean_inc_ref(v_env_437_);
v___x_443_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_441_, v___x_439_, v_env_437_, v_asyncMode_440_, v___x_442_);
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
lean_dec_ref_known(v___x_445_, 1);
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
v___x_489_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_490_ = lean_box(0);
lean_inc_ref(v_env_483_);
v___x_491_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_489_, v___x_487_, v_env_483_, v_asyncMode_488_, v___x_490_);
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
lean_dec_ref_known(v___x_493_, 1);
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
LEAN_EXPORT lean_object* l_Lean_ppLevel(lean_object* v_ctx_526_, lean_object* v_l_527_){
_start:
{
lean_object* v_env_529_; lean_object* v_mctx_530_; lean_object* v_opts_531_; lean_object* v___x_532_; lean_object* v_asyncMode_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_ppLevel_537_; lean_object* v___x_538_; 
v_env_529_ = lean_ctor_get(v_ctx_526_, 0);
v_mctx_530_ = lean_ctor_get(v_ctx_526_, 1);
lean_inc_ref(v_mctx_530_);
v_opts_531_ = lean_ctor_get(v_ctx_526_, 3);
lean_inc_ref(v_opts_531_);
v___x_532_ = l_Lean_ppExt;
v_asyncMode_533_ = lean_ctor_get(v___x_532_, 2);
v___x_534_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_535_ = lean_box(0);
lean_inc_ref(v_env_529_);
v___x_536_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_534_, v___x_532_, v_env_529_, v_asyncMode_533_, v___x_535_);
v_ppLevel_537_ = lean_ctor_get(v___x_536_, 3);
lean_inc_ref(v_ppLevel_537_);
lean_dec(v___x_536_);
lean_inc(v_l_527_);
v___x_538_ = lean_apply_3(v_ppLevel_537_, v_ctx_526_, v_l_527_, lean_box(0));
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; 
lean_dec_ref(v_opts_531_);
lean_dec_ref(v_mctx_530_);
lean_dec(v_l_527_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
return v_a_539_;
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_560_; 
v_a_540_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_560_ == 0)
{
v___x_542_ = v___x_538_;
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; uint8_t v___x_545_; 
v___x_544_ = l_Lean_pp_rawOnError;
v___x_545_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_531_, v___x_544_);
lean_dec_ref(v_opts_531_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; 
lean_del_object(v___x_542_);
lean_dec(v_a_540_);
lean_dec_ref(v_mctx_530_);
lean_dec(v_l_527_);
v___x_546_ = ((lean_object*)(l_Lean_ppLevel___closed__1));
return v___x_546_;
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_547_ = ((lean_object*)(l_Lean_ppLevel___closed__3));
v___x_548_ = lean_io_error_to_string(v_a_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 3);
lean_ctor_set(v___x_542_, 0, v___x_548_);
v___x_550_ = v___x_542_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_559_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_551_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_547_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_box(1);
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_556_, 0, v_mctx_530_);
v___x_557_ = l_Lean_Level_format(v_l_527_, v___x_545_, v___x_556_);
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_555_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppLevel___boxed(lean_object* v_ctx_561_, lean_object* v_l_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_ppLevel(v_ctx_561_, v_l_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal(lean_object* v_ctx_571_, lean_object* v_mvarId_572_){
_start:
{
lean_object* v_env_574_; lean_object* v_opts_575_; lean_object* v___x_576_; lean_object* v_asyncMode_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v_ppGoal_581_; lean_object* v___x_582_; 
v_env_574_ = lean_ctor_get(v_ctx_571_, 0);
v_opts_575_ = lean_ctor_get(v_ctx_571_, 3);
lean_inc_ref(v_opts_575_);
v___x_576_ = l_Lean_ppExt;
v_asyncMode_577_ = lean_ctor_get(v___x_576_, 2);
v___x_578_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_579_ = lean_box(0);
lean_inc_ref(v_env_574_);
v___x_580_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_578_, v___x_576_, v_env_574_, v_asyncMode_577_, v___x_579_);
v_ppGoal_581_ = lean_ctor_get(v___x_580_, 4);
lean_inc_ref(v_ppGoal_581_);
lean_dec(v___x_580_);
lean_inc(v_mvarId_572_);
v___x_582_ = lean_apply_3(v_ppGoal_581_, v_ctx_571_, v_mvarId_572_, lean_box(0));
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; 
lean_dec_ref(v_opts_575_);
lean_dec(v_mvarId_572_);
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_a_583_);
lean_dec_ref_known(v___x_582_, 1);
return v_a_583_;
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_603_; 
v_a_584_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_603_ == 0)
{
v___x_586_ = v___x_582_;
v_isShared_587_ = v_isSharedCheck_603_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_582_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_603_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = l_Lean_pp_rawOnError;
v___x_589_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_575_, v___x_588_);
lean_dec_ref(v_opts_575_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
lean_del_object(v___x_586_);
lean_dec(v_a_584_);
lean_dec(v_mvarId_572_);
v___x_590_ = ((lean_object*)(l_Lean_ppGoal___closed__1));
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_591_ = ((lean_object*)(l_Lean_ppGoal___closed__3));
v___x_592_ = lean_io_error_to_string(v_a_584_);
if (v_isShared_587_ == 0)
{
lean_ctor_set_tag(v___x_586_, 3);
lean_ctor_set(v___x_586_, 0, v___x_592_);
v___x_594_ = v___x_586_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_602_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_595_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_591_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_597_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_595_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_box(1);
v___x_599_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = l_Lean_formatRawGoal(v_mvarId_572_);
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
return v___x_601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ppGoal___boxed(lean_object* v_ctx_604_, lean_object* v_mvarId_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_ppGoal(v_ctx_604_, v_mvarId_605_);
return v_res_607_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_PPExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_InfoTree_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw);
lean_dec_ref(res);
res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_showInfo = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_showInfo);
lean_dec_ref(res);
res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_raw_maxDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_raw_maxDepth);
lean_dec_ref(res);
res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_rawOnError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_rawOnError);
lean_dec_ref(res);
res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ppFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppFnsRef);
lean_dec_ref(res);
res = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
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

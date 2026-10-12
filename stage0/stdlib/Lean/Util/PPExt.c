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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
static const lean_string_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ppExt"};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(198, 21, 42, 65, 89, 234, 71, 46)}};
static const lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppExt;
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_PPContext_unrestricted(lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_52_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_53_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__6_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_));
v___x_55_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_52_, v___x_53_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_56_;
v_res_56_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4_();
return v_res_58_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_76_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_77_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_78_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_));
v___x_79_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_76_, v___x_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_80_;
v_res_80_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4____boxed(lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2448793243____hygCtx___hyg_4_();
return v_res_82_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(lean_object* v_name_83_, lean_object* v_decl_84_, lean_object* v_ref_85_){
_start:
{
lean_object* v_defValue_87_; lean_object* v_descr_88_; lean_object* v_deprecation_x3f_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v_defValue_87_ = lean_ctor_get(v_decl_84_, 0);
v_descr_88_ = lean_ctor_get(v_decl_84_, 1);
v_deprecation_x3f_89_ = lean_ctor_get(v_decl_84_, 2);
lean_inc(v_defValue_87_);
v___x_90_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_90_, 0, v_defValue_87_);
lean_inc(v_deprecation_x3f_89_);
lean_inc_ref(v_descr_88_);
lean_inc_n(v_name_83_, 2);
v___x_91_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_91_, 0, v_name_83_);
lean_ctor_set(v___x_91_, 1, v_ref_85_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
lean_ctor_set(v___x_91_, 3, v_descr_88_);
lean_ctor_set(v___x_91_, 4, v_deprecation_x3f_89_);
v___x_92_ = lean_register_option(v_name_83_, v___x_91_);
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
lean_object* v_unused_101_; 
v_unused_101_ = lean_ctor_get(v___x_92_, 0);
lean_dec(v_unused_101_);
v___x_94_ = v___x_92_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_dec(v___x_92_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
lean_inc(v_defValue_87_);
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_name_83_);
lean_ctor_set(v___x_96_, 1, v_defValue_87_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_name_83_);
v_a_102_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_92_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_92_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_83_ = stack[0].m_obj;
lean_object* v_decl_84_ = stack[1].m_obj;
lean_object* v_ref_85_ = stack[2].m_obj;
lean_object* v_res_110_;
v_res_110_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v_name_83_, v_decl_84_, v_ref_85_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_111_, lean_object* v_decl_112_, lean_object* v_ref_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v_name_111_, v_decl_112_, v_ref_113_);
lean_dec_ref(v_decl_112_);
return v_res_115_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_132_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_133_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_134_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_));
v___x_135_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__spec__0(v___x_132_, v___x_133_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_136_;
v_res_136_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4____boxed(lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3942376209____hygCtx___hyg_4_();
return v_res_138_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_154_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__1_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_155_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__3_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_156_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__4_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_));
v___x_157_ = l_Lean_Option_register___at___00__private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_2520900279____hygCtx___hyg_4__spec__0(v___x_154_, v___x_155_, v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_158_;
v_res_158_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4____boxed(lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_3629515885____hygCtx___hyg_4_();
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
lean_object* l_Lean_instInhabitedPPFns_default___lam__0(lean_object* v_x_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPPFns_default___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_169_ = stack[0].m_obj;
lean_object* v___y_170_ = stack[1].m_obj;
lean_object* v_res_174_;
v_res_174_ = l_Lean_instInhabitedPPFns_default___lam__0(v_x_169_, v___y_170_);
stack->m_obj
 = v_res_174_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__0___boxed(lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_instInhabitedPPFns_default___lam__0(v_x_175_, v___y_176_);
lean_dec_ref(v___y_176_);
lean_dec_ref(v_x_175_);
return v_res_178_;
}
}
lean_object* l_Lean_instInhabitedPPFns_default___lam__1(lean_object* v_x_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPPFns_default___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_179_ = stack[0].m_obj;
lean_object* v___y_180_ = stack[1].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_instInhabitedPPFns_default___lam__1(v_x_179_, v___y_180_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__1___boxed(lean_object* v_x_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_instInhabitedPPFns_default___lam__1(v_x_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v_x_185_);
return v_res_188_;
}
}
lean_object* l_Lean_instInhabitedPPFns_default___lam__2(lean_object* v_x_189_, lean_object* v___y_190_){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPPFns_default___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_189_ = stack[0].m_obj;
lean_object* v___y_190_ = stack[1].m_obj;
lean_object* v_res_194_;
v_res_194_ = l_Lean_instInhabitedPPFns_default___lam__2(v_x_189_, v___y_190_);
stack->m_obj
 = v_res_194_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__2___boxed(lean_object* v_x_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_instInhabitedPPFns_default___lam__2(v_x_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v_x_195_);
return v_res_198_;
}
}
lean_object* l_Lean_instInhabitedPPFns_default___lam__3(lean_object* v_x_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPPFns_default___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_199_ = stack[0].m_obj;
lean_object* v___y_200_ = stack[1].m_obj;
lean_object* v_res_204_;
v_res_204_ = l_Lean_instInhabitedPPFns_default___lam__3(v_x_199_, v___y_200_);
stack->m_obj
 = v_res_204_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__3___boxed(lean_object* v_x_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_instInhabitedPPFns_default___lam__3(v_x_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v_x_205_);
return v_res_208_;
}
}
lean_object* l_Lean_instInhabitedPPFns_default___lam__4(lean_object* v_x_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default___lam__0___closed__1));
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedPPFns_default___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_209_ = stack[0].m_obj;
lean_object* v___y_210_ = stack[1].m_obj;
lean_object* v_res_214_;
v_res_214_ = l_Lean_instInhabitedPPFns_default___lam__4(v_x_209_, v___y_210_);
stack->m_obj
 = v_res_214_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedPPFns_default___lam__4___boxed(lean_object* v_x_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_instInhabitedPPFns_default___lam__4(v_x_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v_x_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(lean_object* v_opts_232_, lean_object* v_opt_233_){
_start:
{
lean_object* v_name_234_; lean_object* v_defValue_235_; lean_object* v_map_236_; lean_object* v___x_237_; 
v_name_234_ = lean_ctor_get(v_opt_233_, 0);
v_defValue_235_ = lean_ctor_get(v_opt_233_, 1);
v_map_236_ = lean_ctor_get(v_opts_232_, 0);
v___x_237_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_236_, v_name_234_);
if (lean_obj_tag(v___x_237_) == 0)
{
lean_inc(v_defValue_235_);
return v_defValue_235_;
}
else
{
lean_object* v_val_238_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_237_, 1);
if (lean_obj_tag(v_val_238_) == 3)
{
lean_object* v_v_239_; 
v_v_239_ = lean_ctor_get(v_val_238_, 0);
lean_inc(v_v_239_);
lean_dec_ref_known(v_val_238_, 1);
return v_v_239_;
}
else
{
lean_dec(v_val_238_);
lean_inc(v_defValue_235_);
return v_defValue_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0___boxed(lean_object* v_opts_240_, lean_object* v_opt_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_240_, v_opt_241_);
lean_dec_ref(v_opt_241_);
lean_dec_ref(v_opts_240_);
return v_res_242_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(lean_object* v_opts_243_, lean_object* v_opt_244_){
_start:
{
lean_object* v_name_245_; lean_object* v_defValue_246_; lean_object* v_map_247_; lean_object* v___x_248_; 
v_name_245_ = lean_ctor_get(v_opt_244_, 0);
v_defValue_246_ = lean_ctor_get(v_opt_244_, 1);
v_map_247_ = lean_ctor_get(v_opts_243_, 0);
v___x_248_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_247_, v_name_245_);
if (lean_obj_tag(v___x_248_) == 0)
{
uint8_t v___x_249_; 
v___x_249_ = lean_unbox(v_defValue_246_);
return v___x_249_;
}
else
{
lean_object* v_val_250_; 
v_val_250_ = lean_ctor_get(v___x_248_, 0);
lean_inc(v_val_250_);
lean_dec_ref_known(v___x_248_, 1);
if (lean_obj_tag(v_val_250_) == 1)
{
uint8_t v_v_251_; 
v_v_251_ = lean_ctor_get_uint8(v_val_250_, 0);
lean_dec_ref_known(v_val_250_, 0);
return v_v_251_;
}
else
{
uint8_t v___x_252_; 
lean_dec(v_val_250_);
v___x_252_ = lean_unbox(v_defValue_246_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_243_ = stack[0].m_obj;
lean_object* v_opt_244_ = stack[1].m_obj;
uint8_t v_res_253_;
v_res_253_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_243_, v_opt_244_);
stack->m_num = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1___boxed(lean_object* v_opts_254_, lean_object* v_opt_255_){
_start:
{
uint8_t v_res_256_; lean_object* v_r_257_; 
v_res_256_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_254_, v_opt_255_);
lean_dec_ref(v_opt_255_);
lean_dec_ref(v_opts_254_);
v_r_257_ = lean_box(v_res_256_);
return v_r_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm(lean_object* v_ctx_258_, lean_object* v_stx_259_){
_start:
{
lean_object* v_opts_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; uint8_t v___x_265_; lean_object* v___x_266_; 
v_opts_260_ = lean_ctor_get(v_ctx_258_, 3);
v___x_261_ = l_Lean_pp_raw_maxDepth;
v___x_262_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__0(v_opts_260_, v___x_261_);
v___x_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
v___x_264_ = l_Lean_pp_raw_showInfo;
v___x_265_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_260_, v___x_264_);
v___x_266_ = l_Lean_Syntax_formatStx(v_stx_259_, v___x_263_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawTerm___boxed(lean_object* v_ctx_267_, lean_object* v_stx_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_formatRawTerm(v_ctx_267_, v_stx_268_);
lean_dec_ref(v_ctx_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatRawGoal(lean_object* v_mvarId_273_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_274_ = ((lean_object*)(l_Lean_formatRawGoal___closed__1));
v___x_275_ = l_Lean_mkMVar(v_mvarId_273_);
v___x_276_ = lean_expr_dbg_to_string(v___x_275_);
lean_dec_ref(v___x_275_);
v___x_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
v___x_278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_274_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
return v___x_278_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_279_, lean_object* v_e_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_282_ = lean_expr_dbg_to_string(v_e_280_);
v___x_283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
v___x_284_ = lean_box(1);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_279_ = stack[0].m_obj;
lean_object* v_e_280_ = stack[1].m_obj;
lean_object* v_res_287_;
v_res_287_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_279_, v_e_280_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_288_, lean_object* v_e_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_288_, v_e_289_);
lean_dec_ref(v_e_289_);
lean_dec_ref(v_x_288_);
return v_res_291_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_292_, lean_object* v_n_293_){
_start:
{
uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = 1;
v___x_296_ = l_Lean_Name_toString(v_n_293_, v___x_295_);
v___x_297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = lean_box(1);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_292_ = stack[0].m_obj;
lean_object* v_n_293_ = stack[1].m_obj;
lean_object* v_res_301_;
v_res_301_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_292_, v_n_293_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_302_, lean_object* v_n_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__1_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_302_, v_n_303_);
lean_dec_ref(v_x_302_);
return v_res_305_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_ctx_306_, lean_object* v_stx_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = l_Lean_formatRawTerm(v_ctx_306_, v_stx_307_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_306_ = stack[0].m_obj;
lean_object* v_stx_307_ = stack[1].m_obj;
lean_object* v_res_311_;
v_res_311_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_306_, v_stx_307_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_ctx_312_, lean_object* v_stx_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__2_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_312_, v_stx_313_);
lean_dec_ref(v_ctx_312_);
return v_res_315_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_ctx_316_, lean_object* v_l_317_){
_start:
{
lean_object* v_mctx_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_mctx_319_ = lean_ctor_get(v_ctx_316_, 1);
lean_inc_ref(v_mctx_319_);
lean_dec_ref(v_ctx_316_);
v___x_320_ = 1;
v___x_321_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_321_, 0, v_mctx_319_);
v___x_322_ = l_Lean_Level_format(v_l_317_, v___x_320_, v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_316_ = stack[0].m_obj;
lean_object* v_l_317_ = stack[1].m_obj;
lean_object* v_res_324_;
v_res_324_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_316_, v_l_317_);
stack->m_obj
 = v_res_324_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_ctx_325_, lean_object* v_l_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__3_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_ctx_325_, v_l_326_);
return v_res_328_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(lean_object* v_x_329_, lean_object* v_mvarId_330_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = l_Lean_formatRawGoal(v_mvarId_330_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_329_ = stack[0].m_obj;
lean_object* v_mvarId_330_ = stack[1].m_obj;
lean_object* v_res_334_;
v_res_334_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_329_, v_mvarId_330_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_x_335_, lean_object* v_mvarId_336_, lean_object* v___y_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__4_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(v_x_335_, v_mvarId_336_);
lean_dec_ref(v_x_335_);
return v_res_338_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__5_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_));
v___x_352_ = lean_st_mk_ref(v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_354_;
v_res_354_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2____boxed(lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_491208886____hygCtx___hyg_2_();
return v_res_356_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(lean_object* v___x_357_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_st_ref_get(v___x_357_);
v___x_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_360_, 0, v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_357_ = stack[0].m_obj;
lean_object* v_res_361_;
v_res_361_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(v___x_357_);
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v___x_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(v___x_362_);
lean_dec(v___x_362_);
return v_res_364_;
}
}
static lean_object* _init_l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_365_; lean_object* v___f_366_; 
v___x_365_ = l_Lean_ppFnsRef;
v___f_366_ = lean_alloc_closure((void*)(l___private_Lean_Util_PPExt_0__Lean_initFn___lam__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_366_, 0, v___x_365_);
return v___f_366_;
}
}
lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; 
v___f_372_ = lean_obj_once(&l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_, &l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__once, _init_l___private_Lean_Util_PPExt_0__Lean_initFn___closed__0_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_);
v___x_373_ = lean_box(0);
v___x_374_ = lean_box(2);
v___x_375_ = ((lean_object*)(l___private_Lean_Util_PPExt_0__Lean_initFn___closed__2_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_));
v___x_376_ = 0;
v___x_377_ = l_Lean_registerEnvExtension___redArg(v___f_372_, v___x_373_, v___x_374_, v___x_375_, v___x_376_, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT void l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_378_;
v_res_378_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2____boxed(lean_object* v_a_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Util_PPExt_0__Lean_initFn_00___x40_Lean_Util_PPExt_1764952756____hygCtx___hyg_2_();
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_PPExt_0__Lean_PPContext_unrestricted(lean_object* v_ctx_381_){
_start:
{
lean_object* v_env_382_; lean_object* v_mctx_383_; lean_object* v_lctx_384_; lean_object* v_opts_385_; lean_object* v_currNamespace_386_; lean_object* v_openDecls_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_396_; 
v_env_382_ = lean_ctor_get(v_ctx_381_, 0);
v_mctx_383_ = lean_ctor_get(v_ctx_381_, 1);
v_lctx_384_ = lean_ctor_get(v_ctx_381_, 2);
v_opts_385_ = lean_ctor_get(v_ctx_381_, 3);
v_currNamespace_386_ = lean_ctor_get(v_ctx_381_, 4);
v_openDecls_387_ = lean_ctor_get(v_ctx_381_, 5);
v_isSharedCheck_396_ = !lean_is_exclusive(v_ctx_381_);
if (v_isSharedCheck_396_ == 0)
{
v___x_389_ = v_ctx_381_;
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_openDecls_387_);
lean_inc(v_currNamespace_386_);
lean_inc(v_opts_385_);
lean_inc(v_lctx_384_);
lean_inc(v_mctx_383_);
lean_inc(v_env_382_);
lean_dec(v_ctx_381_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_396_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = 0;
v___x_392_ = l_Lean_Environment_setRecordingDeps(v_env_382_, v___x_391_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 0, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_mctx_383_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v_lctx_384_);
lean_ctor_set(v_reuseFailAlloc_395_, 3, v_opts_385_);
lean_ctor_set(v_reuseFailAlloc_395_, 4, v_currNamespace_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 5, v_openDecls_387_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
lean_object* l_Lean_ppExprWithInfos(lean_object* v_ctx_409_, lean_object* v_e_410_){
_start:
{
lean_object* v_ctx_412_; lean_object* v_env_413_; lean_object* v_mctx_414_; lean_object* v_opts_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_ctx_412_ = l___private_Lean_Util_PPExt_0__Lean_PPContext_unrestricted(v_ctx_409_);
v_env_413_ = lean_ctor_get(v_ctx_412_, 0);
v_mctx_414_ = lean_ctor_get(v_ctx_412_, 1);
v_opts_415_ = lean_ctor_get(v_ctx_412_, 3);
lean_inc_ref(v_opts_415_);
v___x_416_ = l_Lean_pp_raw;
v___x_417_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v_asyncMode_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v_ppExprWithInfos_423_; lean_object* v___x_424_; 
v___x_418_ = l_Lean_ppExt;
v_asyncMode_419_ = lean_ctor_get(v___x_418_, 2);
v___x_420_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_421_ = lean_box(0);
lean_inc_ref(v_env_413_);
v___x_422_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_420_, v___x_418_, v_env_413_, v_asyncMode_419_, v___x_421_, v___x_417_);
v_ppExprWithInfos_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc_ref(v_ppExprWithInfos_423_);
lean_dec(v___x_422_);
lean_inc_ref(v_e_410_);
v___x_424_ = lean_apply_3(v_ppExprWithInfos_423_, v_ctx_412_, v_e_410_, lean_box(0));
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; 
lean_dec_ref(v_opts_415_);
lean_dec_ref(v_e_410_);
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
return v_a_425_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_448_; 
v_a_426_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_448_ == 0)
{
v___x_428_ = v___x_424_;
v_isShared_429_ = v_isSharedCheck_448_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_a_426_);
lean_dec(v___x_424_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_448_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = l_Lean_pp_rawOnError;
v___x_431_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_415_, v___x_430_);
lean_dec_ref(v_opts_415_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
lean_del_object(v___x_428_);
lean_dec(v_a_426_);
lean_dec_ref(v_e_410_);
v___x_432_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__2));
return v___x_432_;
}
else
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_433_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__4));
v___x_434_ = lean_io_error_to_string(v_a_426_);
if (v_isShared_429_ == 0)
{
lean_ctor_set_tag(v___x_428_, 3);
lean_ctor_set(v___x_428_, 0, v___x_434_);
v___x_436_ = v___x_428_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_434_);
v___x_436_ = v_reuseFailAlloc_447_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_437_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_437_, 0, v___x_433_);
lean_ctor_set(v___x_437_, 1, v___x_436_);
v___x_438_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_439_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_437_);
lean_ctor_set(v___x_439_, 1, v___x_438_);
v___x_440_ = lean_box(1);
v___x_441_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = lean_expr_dbg_to_string(v_e_410_);
lean_dec_ref(v_e_410_);
v___x_443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
v___x_444_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_441_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = lean_box(1);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
}
}
}
}
else
{
lean_object* v___x_449_; lean_object* v_fst_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_460_; 
lean_inc_ref(v_mctx_414_);
lean_dec_ref(v_opts_415_);
lean_dec_ref(v_ctx_412_);
v___x_449_ = l_Lean_instantiateMVarsCore(v_mctx_414_, v_e_410_);
v_fst_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; 
v_unused_461_ = lean_ctor_get(v___x_449_, 1);
lean_dec(v_unused_461_);
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_fst_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_460_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_454_ = lean_expr_dbg_to_string(v_fst_450_);
lean_dec(v_fst_450_);
v___x_455_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = lean_box(1);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_456_);
lean_ctor_set(v___x_452_, 0, v___x_455_);
v___x_458_ = v___x_452_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ppExprWithInfos_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_409_ = stack[0].m_obj;
lean_object* v_e_410_ = stack[1].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lean_ppExprWithInfos(v_ctx_409_, v_e_410_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lean_ppExprWithInfos___boxed(lean_object* v_ctx_463_, lean_object* v_e_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_ppExprWithInfos(v_ctx_463_, v_e_464_);
return v_res_466_;
}
}
lean_object* l_Lean_ppConstNameWithInfos(lean_object* v_ctx_476_, lean_object* v_n_477_){
_start:
{
lean_object* v_ctx_479_; lean_object* v_env_480_; lean_object* v_opts_481_; lean_object* v___x_482_; lean_object* v_asyncMode_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v_ppConstNameWithInfos_488_; lean_object* v___x_489_; 
v_ctx_479_ = l___private_Lean_Util_PPExt_0__Lean_PPContext_unrestricted(v_ctx_476_);
v_env_480_ = lean_ctor_get(v_ctx_479_, 0);
v_opts_481_ = lean_ctor_get(v_ctx_479_, 3);
lean_inc_ref(v_opts_481_);
v___x_482_ = l_Lean_ppExt;
v_asyncMode_483_ = lean_ctor_get(v___x_482_, 2);
v___x_484_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_485_ = lean_box(0);
v___x_486_ = 0;
lean_inc_ref(v_env_480_);
v___x_487_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_484_, v___x_482_, v_env_480_, v_asyncMode_483_, v___x_485_, v___x_486_);
v_ppConstNameWithInfos_488_ = lean_ctor_get(v___x_487_, 1);
lean_inc_ref(v_ppConstNameWithInfos_488_);
lean_dec(v___x_487_);
lean_inc(v_n_477_);
v___x_489_ = lean_apply_3(v_ppConstNameWithInfos_488_, v_ctx_479_, v_n_477_, lean_box(0));
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; 
lean_dec_ref(v_opts_481_);
lean_dec(v_n_477_);
v_a_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v___x_489_, 1);
return v_a_490_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_513_; 
v_a_491_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_513_ == 0)
{
v___x_493_ = v___x_489_;
v_isShared_494_ = v_isSharedCheck_513_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_489_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_513_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = l_Lean_pp_rawOnError;
v___x_496_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_481_, v___x_495_);
lean_dec_ref(v_opts_481_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_del_object(v___x_493_);
lean_dec(v_a_491_);
lean_dec(v_n_477_);
v___x_497_ = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__2));
return v___x_497_;
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
v___x_498_ = ((lean_object*)(l_Lean_ppConstNameWithInfos___closed__4));
v___x_499_ = lean_io_error_to_string(v_a_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set_tag(v___x_493_, 3);
lean_ctor_set(v___x_493_, 0, v___x_499_);
v___x_501_ = v___x_493_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_499_);
v___x_501_ = v_reuseFailAlloc_512_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_502_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_498_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_504_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = lean_box(1);
v___x_506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_504_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
v___x_507_ = l_Lean_Name_toString(v_n_477_, v___x_496_);
v___x_508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
v___x_509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_506_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_box(1);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
return v___x_511_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ppConstNameWithInfos_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_476_ = stack[0].m_obj;
lean_object* v_n_477_ = stack[1].m_obj;
lean_object* v_res_514_;
v_res_514_ = l_Lean_ppConstNameWithInfos(v_ctx_476_, v_n_477_);
stack->m_obj
 = v_res_514_;
}
LEAN_EXPORT lean_object* l_Lean_ppConstNameWithInfos___boxed(lean_object* v_ctx_515_, lean_object* v_n_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_ppConstNameWithInfos(v_ctx_515_, v_n_516_);
return v_res_518_;
}
}
lean_object* l_Lean_ppTerm(lean_object* v_ctx_525_, lean_object* v_stx_526_){
_start:
{
lean_object* v_ctx_528_; lean_object* v_env_529_; lean_object* v_opts_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_ctx_528_ = l___private_Lean_Util_PPExt_0__Lean_PPContext_unrestricted(v_ctx_525_);
v_env_529_ = lean_ctor_get(v_ctx_528_, 0);
v_opts_530_ = lean_ctor_get(v_ctx_528_, 3);
v___x_531_ = l_Lean_pp_raw;
v___x_532_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_530_, v___x_531_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v_asyncMode_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_ppTerm_538_; lean_object* v___x_539_; 
v___x_533_ = l_Lean_ppExt;
v_asyncMode_534_ = lean_ctor_get(v___x_533_, 2);
v___x_535_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_536_ = lean_box(0);
lean_inc_ref(v_env_529_);
v___x_537_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_535_, v___x_533_, v_env_529_, v_asyncMode_534_, v___x_536_, v___x_532_);
v_ppTerm_538_ = lean_ctor_get(v___x_537_, 2);
lean_inc_ref(v_ppTerm_538_);
lean_dec(v___x_537_);
lean_inc(v_stx_526_);
lean_inc_ref(v_ctx_528_);
v___x_539_ = lean_apply_3(v_ppTerm_538_, v_ctx_528_, v_stx_526_, lean_box(0));
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; 
lean_dec_ref(v_ctx_528_);
lean_dec(v_stx_526_);
v_a_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_540_);
lean_dec_ref_known(v___x_539_, 1);
return v_a_540_;
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_560_; 
v_a_541_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_560_ == 0)
{
v___x_543_ = v___x_539_;
v_isShared_544_ = v_isSharedCheck_560_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_539_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_560_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = l_Lean_pp_rawOnError;
v___x_546_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_530_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; 
lean_del_object(v___x_543_);
lean_dec(v_a_541_);
lean_dec_ref(v_ctx_528_);
lean_dec(v_stx_526_);
v___x_547_ = ((lean_object*)(l_Lean_ppTerm___closed__1));
return v___x_547_;
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = ((lean_object*)(l_Lean_ppTerm___closed__3));
v___x_549_ = lean_io_error_to_string(v_a_541_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 3);
lean_ctor_set(v___x_543_, 0, v___x_549_);
v___x_551_ = v___x_543_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_559_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_552_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_548_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_552_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_box(1);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_554_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v___x_557_ = l_Lean_formatRawTerm(v_ctx_528_, v_stx_526_);
lean_dec_ref(v_ctx_528_);
v___x_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
return v___x_558_;
}
}
}
}
}
else
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_formatRawTerm(v_ctx_528_, v_stx_526_);
lean_dec_ref(v_ctx_528_);
return v___x_561_;
}
}
}
LEAN_EXPORT void l_Lean_ppTerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_525_ = stack[0].m_obj;
lean_object* v_stx_526_ = stack[1].m_obj;
lean_object* v_res_562_;
v_res_562_ = l_Lean_ppTerm(v_ctx_525_, v_stx_526_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l_Lean_ppTerm___boxed(lean_object* v_ctx_563_, lean_object* v_stx_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_ppTerm(v_ctx_563_, v_stx_564_);
return v_res_566_;
}
}
lean_object* l_Lean_ppLevel(lean_object* v_ctx_573_, lean_object* v_l_574_){
_start:
{
lean_object* v_ctx_576_; lean_object* v_env_577_; lean_object* v_mctx_578_; lean_object* v_opts_579_; lean_object* v___x_580_; lean_object* v_asyncMode_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; lean_object* v_ppLevel_586_; lean_object* v___x_587_; 
v_ctx_576_ = l___private_Lean_Util_PPExt_0__Lean_PPContext_unrestricted(v_ctx_573_);
v_env_577_ = lean_ctor_get(v_ctx_576_, 0);
v_mctx_578_ = lean_ctor_get(v_ctx_576_, 1);
lean_inc_ref(v_mctx_578_);
v_opts_579_ = lean_ctor_get(v_ctx_576_, 3);
lean_inc_ref(v_opts_579_);
v___x_580_ = l_Lean_ppExt;
v_asyncMode_581_ = lean_ctor_get(v___x_580_, 2);
v___x_582_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_583_ = lean_box(0);
v___x_584_ = 0;
lean_inc_ref(v_env_577_);
v___x_585_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_582_, v___x_580_, v_env_577_, v_asyncMode_581_, v___x_583_, v___x_584_);
v_ppLevel_586_ = lean_ctor_get(v___x_585_, 3);
lean_inc_ref(v_ppLevel_586_);
lean_dec(v___x_585_);
lean_inc(v_l_574_);
v___x_587_ = lean_apply_3(v_ppLevel_586_, v_ctx_576_, v_l_574_, lean_box(0));
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v_a_588_; 
lean_dec_ref(v_opts_579_);
lean_dec_ref(v_mctx_578_);
lean_dec(v_l_574_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref_known(v___x_587_, 1);
return v_a_588_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_609_; 
v_a_589_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_609_ == 0)
{
v___x_591_ = v___x_587_;
v_isShared_592_ = v_isSharedCheck_609_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_609_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = l_Lean_pp_rawOnError;
v___x_594_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_579_, v___x_593_);
lean_dec_ref(v_opts_579_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; 
lean_del_object(v___x_591_);
lean_dec(v_a_589_);
lean_dec_ref(v_mctx_578_);
lean_dec(v_l_574_);
v___x_595_ = ((lean_object*)(l_Lean_ppLevel___closed__1));
return v___x_595_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_596_ = ((lean_object*)(l_Lean_ppLevel___closed__3));
v___x_597_ = lean_io_error_to_string(v_a_589_);
if (v_isShared_592_ == 0)
{
lean_ctor_set_tag(v___x_591_, 3);
lean_ctor_set(v___x_591_, 0, v___x_597_);
v___x_599_ = v___x_591_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_597_);
v___x_599_ = v_reuseFailAlloc_608_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_596_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_602_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = lean_box(1);
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_alloc_closure((void*)(l_Lean_MetavarContext_findLevelIndex_x3f___boxed), 2, 1);
lean_closure_set(v___x_605_, 0, v_mctx_578_);
v___x_606_ = l_Lean_Level_format(v_l_574_, v___x_594_, v___x_605_);
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_604_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
return v___x_607_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ppLevel_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_573_ = stack[0].m_obj;
lean_object* v_l_574_ = stack[1].m_obj;
lean_object* v_res_610_;
v_res_610_ = l_Lean_ppLevel(v_ctx_573_, v_l_574_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_ppLevel___boxed(lean_object* v_ctx_611_, lean_object* v_l_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_ppLevel(v_ctx_611_, v_l_612_);
return v_res_614_;
}
}
lean_object* l_Lean_ppGoal(lean_object* v_ctx_621_, lean_object* v_mvarId_622_){
_start:
{
lean_object* v_ctx_624_; lean_object* v_env_625_; lean_object* v_opts_626_; lean_object* v___x_627_; lean_object* v_asyncMode_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v_ppGoal_633_; lean_object* v___x_634_; 
v_ctx_624_ = l___private_Lean_Util_PPExt_0__Lean_PPContext_unrestricted(v_ctx_621_);
v_env_625_ = lean_ctor_get(v_ctx_624_, 0);
v_opts_626_ = lean_ctor_get(v_ctx_624_, 3);
lean_inc_ref(v_opts_626_);
v___x_627_ = l_Lean_ppExt;
v_asyncMode_628_ = lean_ctor_get(v___x_627_, 2);
v___x_629_ = ((lean_object*)(l_Lean_instInhabitedPPFns_default));
v___x_630_ = lean_box(0);
v___x_631_ = 0;
lean_inc_ref(v_env_625_);
v___x_632_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_629_, v___x_627_, v_env_625_, v_asyncMode_628_, v___x_630_, v___x_631_);
v_ppGoal_633_ = lean_ctor_get(v___x_632_, 4);
lean_inc_ref(v_ppGoal_633_);
lean_dec(v___x_632_);
lean_inc(v_mvarId_622_);
v___x_634_ = lean_apply_3(v_ppGoal_633_, v_ctx_624_, v_mvarId_622_, lean_box(0));
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; 
lean_dec_ref(v_opts_626_);
lean_dec(v_mvarId_622_);
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
return v_a_635_;
}
else
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_655_; 
v_a_636_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_655_ == 0)
{
v___x_638_ = v___x_634_;
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_634_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_655_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = l_Lean_pp_rawOnError;
v___x_641_ = l_Lean_Option_get___at___00Lean_formatRawTerm_spec__1(v_opts_626_, v___x_640_);
lean_dec_ref(v_opts_626_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_del_object(v___x_638_);
lean_dec(v_a_636_);
lean_dec(v_mvarId_622_);
v___x_642_ = ((lean_object*)(l_Lean_ppGoal___closed__1));
return v___x_642_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_643_ = ((lean_object*)(l_Lean_ppGoal___closed__3));
v___x_644_ = lean_io_error_to_string(v_a_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set_tag(v___x_638_, 3);
lean_ctor_set(v___x_638_, 0, v___x_644_);
v___x_646_ = v___x_638_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_654_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_643_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = ((lean_object*)(l_Lean_ppExprWithInfos___closed__6));
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = lean_box(1);
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_649_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_Lean_formatRawGoal(v_mvarId_622_);
v___x_653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
return v___x_653_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ppGoal_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_621_ = stack[0].m_obj;
lean_object* v_mvarId_622_ = stack[1].m_obj;
lean_object* v_res_656_;
v_res_656_ = l_Lean_ppGoal(v_ctx_621_, v_mvarId_622_);
stack->m_obj
 = v_res_656_;
}
LEAN_EXPORT lean_object* l_Lean_ppGoal___boxed(lean_object* v_ctx_657_, lean_object* v_mvarId_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_ppGoal(v_ctx_657_, v_mvarId_658_);
return v_res_660_;
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

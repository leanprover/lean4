// Lean compiler output
// Module: Lake.Config.ConfigDecl
// Imports: public import Lake.Config.Opaque public import Lake.Config.LeanLibConfig public import Lake.Config.LeanExeConfig public import Lake.Config.ExternLibConfig public import Lake.Config.InputFileConfig import Lake.Util.Name
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lake_ExternLib_keyword;
extern lean_object* l_Lake_LeanExe_keyword;
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static const lean_string_object l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_ = (const lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value;
static const lean_string_object l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ConfigDecl"};
static const lean_object* l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_ = (const lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value;
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value),LEAN_SCALAR_PTR_LITERAL(19, 115, 72, 196, 55, 38, 211, 152)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameConfigDecl = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value;
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4_value;
static const lean_array_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5_value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value;
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7_value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value;
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9_value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value;
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11_value;
static const lean_string_object l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12 = (const lean_object*)&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12_value;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20;
static lean_once_cell_t l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21;
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_pkg__eq___autoParam;
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_name__eq___autoParam;
LEAN_EXPORT lean_object* l_Lake_KConfigDecl_kind__eq___autoParam;
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_partialKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_partialKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0 = (const lean_object*)&l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0 = (const lean_object*)&l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value;
static const lean_ctor_object l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_ConfigDecl_leanLibConfig_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 123, 8, 14, 20, 41, 164, 170)}};
static const lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1 = (const lean_object*)&l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_lib"};
static const lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0 = (const lean_object*)&l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0_value;
static const lean_string_object l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lean_exe"};
static const lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1 = (const lean_object*)&l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "extern_lib"};
static const lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2 = (const lean_object*)&l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2_value;
static const lean_string_object l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "input_file"};
static const lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3 = (const lean_object*)&l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3_value;
static const lean_string_object l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "input_dir"};
static const lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4 = (const lean_object*)&l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LeanLibDecl"};
static const lean_object* l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value;
static const lean_ctor_object l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value_aux_0),((lean_object*)&l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 139, 151, 247, 81, 186, 255, 54)}};
static const lean_object* l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameLeanLibDecl_unsafe__1 = (const lean_object*)&l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameLeanLibDecl = (const lean_object*)&l_Lake_instTypeNameLeanLibDecl_unsafe__1___closed__1_value;
static const lean_string_object l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "LeanExeDecl"};
static const lean_object* l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value;
static const lean_ctor_object l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value_aux_0),((lean_object*)&l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 3, 79, 186, 100, 200, 233, 30)}};
static const lean_object* l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameLeanExeDecl_unsafe__1 = (const lean_object*)&l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameLeanExeDecl = (const lean_object*)&l_Lake_instTypeNameLeanExeDecl_unsafe__1___closed__1_value;
static const lean_string_object l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "InputFileDecl"};
static const lean_object* l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value;
static const lean_ctor_object l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value_aux_0),((lean_object*)&l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(186, 159, 223, 49, 71, 15, 73, 230)}};
static const lean_object* l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameInputFileDecl_unsafe__1 = (const lean_object*)&l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameInputFileDecl = (const lean_object*)&l_Lake_instTypeNameInputFileDecl_unsafe__1___closed__1_value;
static const lean_string_object l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "InputDirDecl"};
static const lean_object* l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value;
static const lean_ctor_object l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_ConfigDecl_1050678479____hygCtx___hyg_43__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value_aux_0),((lean_object*)&l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 100, 97, 166, 219, 82, 104, 152)}};
static const lean_object* l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameInputDirDecl_unsafe__1 = (const lean_object*)&l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameInputDirDecl = (const lean_object*)&l_Lake_instTypeNameInputDirDecl_unsafe__1___closed__1_value;
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__12));
v___x_36_ = l_Lean_mkAtom(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__13);
v___x_38_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5));
v___x_39_ = lean_array_push(v___x_38_, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_40_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__14);
v___x_41_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__11));
v___x_42_ = lean_box(2);
v___x_43_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
lean_ctor_set(v___x_43_, 2, v___x_40_);
return v___x_43_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__15);
v___x_45_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5));
v___x_46_ = lean_array_push(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_47_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__16);
v___x_48_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__9));
v___x_49_ = lean_box(2);
v___x_50_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
lean_ctor_set(v___x_50_, 1, v___x_48_);
lean_ctor_set(v___x_50_, 2, v___x_47_);
return v___x_50_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__17);
v___x_52_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5));
v___x_53_ = lean_array_push(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__18);
v___x_55_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__7));
v___x_56_ = lean_box(2);
v___x_57_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
lean_ctor_set(v___x_57_, 2, v___x_54_);
return v___x_57_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__19);
v___x_59_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__5));
v___x_60_ = lean_array_push(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_61_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__20);
v___x_62_ = ((lean_object*)(l_Lake_PConfigDecl_pkg__eq___autoParam___closed__4));
v___x_63_ = lean_box(2);
v___x_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___x_62_);
lean_ctor_set(v___x_64_, 2, v___x_61_);
return v___x_64_;
}
}
static lean_object* _init_l_Lake_PConfigDecl_pkg__eq___autoParam(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21);
return v___x_65_;
}
}
static lean_object* _init_l_Lake_NConfigDecl_name__eq___autoParam(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21);
return v___x_66_;
}
}
static lean_object* _init_l_Lake_KConfigDecl_kind__eq___autoParam(void){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_obj_once(&l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21, &l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21_once, _init_l_Lake_PConfigDecl_pkg__eq___autoParam___closed__21);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_partialKey(lean_object* v_self_68_){
_start:
{
lean_object* v_name_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_name_69_ = lean_ctor_get(v_self_68_, 1);
v___x_70_ = lean_box(0);
lean_inc(v_name_69_);
v___x_71_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_name_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_partialKey___boxed(lean_object* v_self_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lake_ConfigDecl_partialKey(v_self_72_);
lean_dec_ref(v_self_72_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0(lean_object* v_x_74_){
_start:
{
lean_object* v_name_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_name_75_ = lean_ctor_get(v_x_74_, 1);
v___x_76_ = lean_box(0);
lean_inc(v_name_75_);
v___x_77_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v_name_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0___boxed(lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___lam__0(v_x_78_);
lean_dec_ref(v_x_78_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey(lean_object* v_k_81_){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = ((lean_object*)(l_Lake_instCoeOutKConfigDeclPartialBuildKey___closed__0));
return v___f_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___boxed(lean_object* v_k_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey(v_k_83_);
lean_dec(v_k_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg(lean_object* v_self_85_){
_start:
{
lean_object* v_config_86_; 
v_config_86_ = lean_ctor_get(v_self_85_, 3);
lean_inc(v_config_86_);
return v_config_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg___boxed(lean_object* v_self_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lake_PConfigDecl_config_x27___redArg(v_self_87_);
lean_dec_ref(v_self_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27(lean_object* v_p_89_, lean_object* v_self_90_){
_start:
{
lean_object* v_config_91_; 
v_config_91_ = lean_ctor_get(v_self_90_, 3);
lean_inc(v_config_91_);
return v_config_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___boxed(lean_object* v_p_92_, lean_object* v_self_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lake_PConfigDecl_config_x27(v_p_92_, v_self_93_);
lean_dec_ref(v_self_93_);
lean_dec(v_p_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg(lean_object* v_self_95_){
_start:
{
lean_object* v_config_96_; 
v_config_96_ = lean_ctor_get(v_self_95_, 3);
lean_inc(v_config_96_);
return v_config_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg___boxed(lean_object* v_self_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lake_NConfigDecl_config_x27___redArg(v_self_97_);
lean_dec_ref(v_self_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27(lean_object* v_p_99_, lean_object* v_n_100_, lean_object* v_self_101_){
_start:
{
lean_object* v_config_102_; 
v_config_102_ = lean_ctor_get(v_self_101_, 3);
lean_inc(v_config_102_);
return v_config_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___boxed(lean_object* v_p_103_, lean_object* v_n_104_, lean_object* v_self_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lake_NConfigDecl_config_x27(v_p_103_, v_n_104_, v_self_105_);
lean_dec_ref(v_self_105_);
lean_dec(v_n_104_);
lean_dec(v_p_103_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f(lean_object* v_kind_107_, lean_object* v_self_108_){
_start:
{
lean_object* v_kind_109_; lean_object* v_config_110_; uint8_t v___x_111_; 
v_kind_109_ = lean_ctor_get(v_self_108_, 2);
v_config_110_ = lean_ctor_get(v_self_108_, 3);
v___x_111_ = lean_name_eq(v_kind_109_, v_kind_107_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_box(0);
return v___x_112_;
}
else
{
lean_object* v___x_113_; 
lean_inc(v_config_110_);
v___x_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_113_, 0, v_config_110_);
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f___boxed(lean_object* v_kind_114_, lean_object* v_self_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lake_ConfigDecl_config_x3f(v_kind_114_, v_self_115_);
lean_dec_ref(v_self_115_);
lean_dec(v_kind_114_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg(lean_object* v_kind_117_, lean_object* v_self_118_){
_start:
{
lean_object* v_kind_119_; lean_object* v_config_120_; uint8_t v___x_121_; 
v_kind_119_ = lean_ctor_get(v_self_118_, 2);
v_config_120_ = lean_ctor_get(v_self_118_, 3);
v___x_121_ = lean_name_eq(v_kind_119_, v_kind_117_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_box(0);
return v___x_122_;
}
else
{
lean_object* v___x_123_; 
lean_inc(v_config_120_);
v___x_123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_123_, 0, v_config_120_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg___boxed(lean_object* v_kind_124_, lean_object* v_self_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lake_PConfigDecl_config_x3f___redArg(v_kind_124_, v_self_125_);
lean_dec_ref(v_self_125_);
lean_dec(v_kind_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f(lean_object* v_p_127_, lean_object* v_kind_128_, lean_object* v_self_129_){
_start:
{
lean_object* v_kind_130_; lean_object* v_config_131_; uint8_t v___x_132_; 
v_kind_130_ = lean_ctor_get(v_self_129_, 2);
v_config_131_ = lean_ctor_get(v_self_129_, 3);
v___x_132_ = lean_name_eq(v_kind_130_, v_kind_128_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_box(0);
return v___x_133_;
}
else
{
lean_object* v___x_134_; 
lean_inc(v_config_131_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v_config_131_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___boxed(lean_object* v_p_135_, lean_object* v_kind_136_, lean_object* v_self_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lake_PConfigDecl_config_x3f(v_p_135_, v_kind_136_, v_self_137_);
lean_dec_ref(v_self_137_);
lean_dec(v_kind_136_);
lean_dec(v_p_135_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg(lean_object* v_kind_139_, lean_object* v_self_140_){
_start:
{
lean_object* v_kind_141_; lean_object* v_config_142_; uint8_t v___x_143_; 
v_kind_141_ = lean_ctor_get(v_self_140_, 2);
v_config_142_ = lean_ctor_get(v_self_140_, 3);
v___x_143_ = lean_name_eq(v_kind_141_, v_kind_139_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_box(0);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
lean_inc(v_config_142_);
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v_config_142_);
return v___x_145_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg___boxed(lean_object* v_kind_146_, lean_object* v_self_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lake_NConfigDecl_config_x3f___redArg(v_kind_146_, v_self_147_);
lean_dec_ref(v_self_147_);
lean_dec(v_kind_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f(lean_object* v_p_149_, lean_object* v_n_150_, lean_object* v_kind_151_, lean_object* v_self_152_){
_start:
{
lean_object* v_kind_153_; lean_object* v_config_154_; uint8_t v___x_155_; 
v_kind_153_ = lean_ctor_get(v_self_152_, 2);
v_config_154_ = lean_ctor_get(v_self_152_, 3);
v___x_155_ = lean_name_eq(v_kind_153_, v_kind_151_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_box(0);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
lean_inc(v_config_154_);
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v_config_154_);
return v___x_157_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___boxed(lean_object* v_p_158_, lean_object* v_n_159_, lean_object* v_kind_160_, lean_object* v_self_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lake_NConfigDecl_config_x3f(v_p_158_, v_n_159_, v_kind_160_, v_self_161_);
lean_dec_ref(v_self_161_);
lean_dec(v_kind_160_);
lean_dec(v_n_159_);
lean_dec(v_p_158_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f(lean_object* v_self_166_){
_start:
{
lean_object* v_kind_167_; lean_object* v_config_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v_kind_167_ = lean_ctor_get(v_self_166_, 2);
v_config_168_ = lean_ctor_get(v_self_166_, 3);
v___x_169_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_170_ = lean_name_eq(v_kind_167_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
return v___x_171_;
}
else
{
lean_object* v___x_172_; 
lean_inc(v_config_168_);
v___x_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_172_, 0, v_config_168_);
return v___x_172_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f___boxed(lean_object* v_self_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lake_ConfigDecl_leanLibConfig_x3f(v_self_173_);
lean_dec_ref(v_self_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(lean_object* v_self_175_){
_start:
{
lean_object* v_kind_176_; lean_object* v_config_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_kind_176_ = lean_ctor_get(v_self_175_, 2);
v_config_177_ = lean_ctor_get(v_self_175_, 3);
v___x_178_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_179_ = lean_name_eq(v_kind_176_, v___x_178_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
v___x_180_ = lean_box(0);
return v___x_180_;
}
else
{
lean_object* v___x_181_; 
lean_inc(v_config_177_);
v___x_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_181_, 0, v_config_177_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg___boxed(lean_object* v_self_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(v_self_182_);
lean_dec_ref(v_self_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f(lean_object* v_p_184_, lean_object* v_n_185_, lean_object* v_self_186_){
_start:
{
lean_object* v_kind_187_; lean_object* v_config_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_kind_187_ = lean_ctor_get(v_self_186_, 2);
v_config_188_ = lean_ctor_get(v_self_186_, 3);
v___x_189_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_190_ = lean_name_eq(v_kind_187_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
else
{
lean_object* v___x_192_; 
lean_inc(v_config_188_);
v___x_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_192_, 0, v_config_188_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___boxed(lean_object* v_p_193_, lean_object* v_n_194_, lean_object* v_self_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lake_NConfigDecl_leanLibConfig_x3f(v_p_193_, v_n_194_, v_self_195_);
lean_dec_ref(v_self_195_);
lean_dec(v_n_194_);
lean_dec(v_p_193_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f(lean_object* v_self_197_){
_start:
{
lean_object* v_kind_198_; lean_object* v_config_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_kind_198_ = lean_ctor_get(v_self_197_, 2);
v_config_199_ = lean_ctor_get(v_self_197_, 3);
v___x_200_ = l_Lake_LeanExe_keyword;
v___x_201_ = lean_name_eq(v_kind_198_, v___x_200_);
if (v___x_201_ == 0)
{
lean_object* v___x_202_; 
v___x_202_ = lean_box(0);
return v___x_202_;
}
else
{
lean_object* v___x_203_; 
lean_inc(v_config_199_);
v___x_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_203_, 0, v_config_199_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f___boxed(lean_object* v_self_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lake_ConfigDecl_leanExeConfig_x3f(v_self_204_);
lean_dec_ref(v_self_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(lean_object* v_self_206_){
_start:
{
lean_object* v_kind_207_; lean_object* v_config_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_kind_207_ = lean_ctor_get(v_self_206_, 2);
v_config_208_ = lean_ctor_get(v_self_206_, 3);
v___x_209_ = l_Lake_LeanExe_keyword;
v___x_210_ = lean_name_eq(v_kind_207_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_box(0);
return v___x_211_;
}
else
{
lean_object* v___x_212_; 
lean_inc(v_config_208_);
v___x_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_212_, 0, v_config_208_);
return v___x_212_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg___boxed(lean_object* v_self_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(v_self_213_);
lean_dec_ref(v_self_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f(lean_object* v_p_215_, lean_object* v_n_216_, lean_object* v_self_217_){
_start:
{
lean_object* v_kind_218_; lean_object* v_config_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_kind_218_ = lean_ctor_get(v_self_217_, 2);
v_config_219_ = lean_ctor_get(v_self_217_, 3);
v___x_220_ = l_Lake_LeanExe_keyword;
v___x_221_ = lean_name_eq(v_kind_218_, v___x_220_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v___x_223_; 
lean_inc(v_config_219_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_config_219_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___boxed(lean_object* v_p_224_, lean_object* v_n_225_, lean_object* v_self_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lake_NConfigDecl_leanExeConfig_x3f(v_p_224_, v_n_225_, v_self_226_);
lean_dec_ref(v_self_226_);
lean_dec(v_n_225_);
lean_dec(v_p_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg(lean_object* v_self_228_){
_start:
{
lean_object* v_kind_229_; lean_object* v_config_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v_kind_229_ = lean_ctor_get(v_self_228_, 2);
v_config_230_ = lean_ctor_get(v_self_228_, 3);
v___x_231_ = l_Lake_ExternLib_keyword;
v___x_232_ = lean_name_eq(v_kind_229_, v___x_231_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v___x_234_; 
lean_inc(v_config_230_);
v___x_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_234_, 0, v_config_230_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object* v_self_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lake_PConfigDecl_externLibConfig_x3f___redArg(v_self_235_);
lean_dec_ref(v_self_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f(lean_object* v_p_237_, lean_object* v_self_238_){
_start:
{
lean_object* v_kind_239_; lean_object* v_config_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v_kind_239_ = lean_ctor_get(v_self_238_, 2);
v_config_240_ = lean_ctor_get(v_self_238_, 3);
v___x_241_ = l_Lake_ExternLib_keyword;
v___x_242_ = lean_name_eq(v_kind_239_, v___x_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(0);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
lean_inc(v_config_240_);
v___x_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_244_, 0, v_config_240_);
return v___x_244_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___boxed(lean_object* v_p_245_, lean_object* v_self_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_PConfigDecl_externLibConfig_x3f(v_p_245_, v_self_246_);
lean_dec_ref(v_self_246_);
lean_dec(v_p_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg(lean_object* v_self_248_){
_start:
{
lean_object* v_kind_249_; lean_object* v_config_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_kind_249_ = lean_ctor_get(v_self_248_, 2);
v_config_250_ = lean_ctor_get(v_self_248_, 3);
v___x_251_ = l_Lake_ExternLib_keyword;
v___x_252_ = lean_name_eq(v_kind_249_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
v___x_253_ = lean_box(0);
return v___x_253_;
}
else
{
lean_object* v___x_254_; 
lean_inc(v_config_250_);
v___x_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_254_, 0, v_config_250_);
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object* v_self_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lake_NConfigDecl_externLibConfig_x3f___redArg(v_self_255_);
lean_dec_ref(v_self_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f(lean_object* v_p_257_, lean_object* v_n_258_, lean_object* v_self_259_){
_start:
{
lean_object* v_kind_260_; lean_object* v_config_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_kind_260_ = lean_ctor_get(v_self_259_, 2);
v_config_261_ = lean_ctor_get(v_self_259_, 3);
v___x_262_ = l_Lake_ExternLib_keyword;
v___x_263_ = lean_name_eq(v_kind_260_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v___x_265_; 
lean_inc(v_config_261_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_config_261_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___boxed(lean_object* v_p_266_, lean_object* v_n_267_, lean_object* v_self_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lake_NConfigDecl_externLibConfig_x3f(v_p_266_, v_n_267_, v_self_268_);
lean_dec_ref(v_self_268_);
lean_dec(v_n_267_);
lean_dec(v_p_266_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg(lean_object* v_kind_275_, lean_object* v_h__1_276_, lean_object* v_h__2_277_, lean_object* v_h__3_278_, lean_object* v_h__4_279_, lean_object* v_h__5_280_, lean_object* v_h__6_281_, lean_object* v_h__7_282_){
_start:
{
switch(lean_obj_tag(v_kind_275_))
{
case 1:
{
lean_object* v_pre_283_; 
lean_dec(v_h__4_279_);
v_pre_283_ = lean_ctor_get(v_kind_275_, 0);
if (lean_obj_tag(v_pre_283_) == 0)
{
lean_object* v_str_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_str_284_ = lean_ctor_get(v_kind_275_, 1);
v___x_285_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0));
v___x_286_ = lean_string_dec_eq(v_str_284_, v___x_285_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; uint8_t v___x_288_; 
lean_dec(v_h__1_276_);
v___x_287_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1));
v___x_288_ = lean_string_dec_eq(v_str_284_, v___x_287_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; uint8_t v___x_290_; 
lean_dec(v_h__2_277_);
v___x_289_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2));
v___x_290_ = lean_string_dec_eq(v_str_284_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
lean_dec(v_h__3_278_);
v___x_291_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3));
v___x_292_ = lean_string_dec_eq(v_str_284_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
lean_dec(v_h__5_280_);
v___x_293_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4));
v___x_294_ = lean_string_dec_eq(v_str_284_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
lean_dec(v_h__6_281_);
v___x_295_ = lean_apply_7(v_h__7_282_, v_kind_275_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_295_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec_ref(v_kind_275_);
lean_dec(v_h__7_282_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_apply_1(v_h__6_281_, v___x_296_);
return v___x_297_;
}
}
else
{
lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v_kind_275_);
lean_dec(v_h__7_282_);
lean_dec(v_h__6_281_);
v___x_298_ = lean_box(0);
v___x_299_ = lean_apply_1(v_h__5_280_, v___x_298_);
return v___x_299_;
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref(v_kind_275_);
lean_dec(v_h__7_282_);
lean_dec(v_h__6_281_);
lean_dec(v_h__5_280_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__3_278_, v___x_300_);
return v___x_301_;
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_kind_275_);
lean_dec(v_h__7_282_);
lean_dec(v_h__6_281_);
lean_dec(v_h__5_280_);
lean_dec(v_h__3_278_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_apply_1(v_h__2_277_, v___x_302_);
return v___x_303_;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_kind_275_);
lean_dec(v_h__7_282_);
lean_dec(v_h__6_281_);
lean_dec(v_h__5_280_);
lean_dec(v_h__3_278_);
lean_dec(v_h__2_277_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v_h__1_276_, v___x_304_);
return v___x_305_;
}
}
else
{
lean_object* v___x_306_; 
lean_dec(v_h__6_281_);
lean_dec(v_h__5_280_);
lean_dec(v_h__3_278_);
lean_dec(v_h__2_277_);
lean_dec(v_h__1_276_);
v___x_306_ = lean_apply_7(v_h__7_282_, v_kind_275_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_306_;
}
}
case 0:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_h__7_282_);
lean_dec(v_h__6_281_);
lean_dec(v_h__5_280_);
lean_dec(v_h__3_278_);
lean_dec(v_h__2_277_);
lean_dec(v_h__1_276_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_1(v_h__4_279_, v___x_307_);
return v___x_308_;
}
default: 
{
lean_object* v___x_309_; 
lean_dec(v_h__6_281_);
lean_dec(v_h__5_280_);
lean_dec(v_h__4_279_);
lean_dec(v_h__3_278_);
lean_dec(v_h__2_277_);
lean_dec(v_h__1_276_);
v___x_309_ = lean_apply_7(v_h__7_282_, v_kind_275_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_309_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter(lean_object* v_motive_310_, lean_object* v_kind_311_, lean_object* v_h__1_312_, lean_object* v_h__2_313_, lean_object* v_h__3_314_, lean_object* v_h__4_315_, lean_object* v_h__5_316_, lean_object* v_h__6_317_, lean_object* v_h__7_318_){
_start:
{
switch(lean_obj_tag(v_kind_311_))
{
case 1:
{
lean_object* v_pre_319_; 
lean_dec(v_h__4_315_);
v_pre_319_ = lean_ctor_get(v_kind_311_, 0);
if (lean_obj_tag(v_pre_319_) == 0)
{
lean_object* v_str_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v_str_320_ = lean_ctor_get(v_kind_311_, 1);
v___x_321_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0));
v___x_322_ = lean_string_dec_eq(v_str_320_, v___x_321_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; uint8_t v___x_324_; 
lean_dec(v_h__1_312_);
v___x_323_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1));
v___x_324_ = lean_string_dec_eq(v_str_320_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
lean_dec(v_h__2_313_);
v___x_325_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2));
v___x_326_ = lean_string_dec_eq(v_str_320_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
lean_dec(v_h__3_314_);
v___x_327_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3));
v___x_328_ = lean_string_dec_eq(v_str_320_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
lean_dec(v_h__5_316_);
v___x_329_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4));
v___x_330_ = lean_string_dec_eq(v_str_320_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
lean_dec(v_h__6_317_);
v___x_331_ = lean_apply_7(v_h__7_318_, v_kind_311_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec_ref(v_kind_311_);
lean_dec(v_h__7_318_);
v___x_332_ = lean_box(0);
v___x_333_ = lean_apply_1(v_h__6_317_, v___x_332_);
return v___x_333_;
}
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; 
lean_dec_ref(v_kind_311_);
lean_dec(v_h__7_318_);
lean_dec(v_h__6_317_);
v___x_334_ = lean_box(0);
v___x_335_ = lean_apply_1(v_h__5_316_, v___x_334_);
return v___x_335_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v_kind_311_);
lean_dec(v_h__7_318_);
lean_dec(v_h__6_317_);
lean_dec(v_h__5_316_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_apply_1(v_h__3_314_, v___x_336_);
return v___x_337_;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref(v_kind_311_);
lean_dec(v_h__7_318_);
lean_dec(v_h__6_317_);
lean_dec(v_h__5_316_);
lean_dec(v_h__3_314_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_apply_1(v_h__2_313_, v___x_338_);
return v___x_339_;
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref(v_kind_311_);
lean_dec(v_h__7_318_);
lean_dec(v_h__6_317_);
lean_dec(v_h__5_316_);
lean_dec(v_h__3_314_);
lean_dec(v_h__2_313_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_apply_1(v_h__1_312_, v___x_340_);
return v___x_341_;
}
}
else
{
lean_object* v___x_342_; 
lean_dec(v_h__6_317_);
lean_dec(v_h__5_316_);
lean_dec(v_h__3_314_);
lean_dec(v_h__2_313_);
lean_dec(v_h__1_312_);
v___x_342_ = lean_apply_7(v_h__7_318_, v_kind_311_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_342_;
}
}
case 0:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_h__7_318_);
lean_dec(v_h__6_317_);
lean_dec(v_h__5_316_);
lean_dec(v_h__3_314_);
lean_dec(v_h__2_313_);
lean_dec(v_h__1_312_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_apply_1(v_h__4_315_, v___x_343_);
return v___x_344_;
}
default: 
{
lean_object* v___x_345_; 
lean_dec(v_h__6_317_);
lean_dec(v_h__5_316_);
lean_dec(v_h__4_315_);
lean_dec(v_h__3_314_);
lean_dec(v_h__2_313_);
lean_dec(v_h__1_312_);
v___x_345_ = lean_apply_7(v_h__7_318_, v_kind_311_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg(lean_object* v_self_346_){
_start:
{
lean_object* v_config_347_; 
v_config_347_ = lean_ctor_get(v_self_346_, 3);
lean_inc(v_config_347_);
return v_config_347_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object* v_self_348_){
_start:
{
lean_object* v_res_349_; 
v_res_349_ = l_Lake_PConfigDecl_opaqueTargetConfig___redArg(v_self_348_);
lean_dec_ref(v_self_348_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig(lean_object* v_p_350_, lean_object* v_self_351_, lean_object* v_h_352_){
_start:
{
lean_object* v_config_353_; 
v_config_353_ = lean_ctor_get(v_self_351_, 3);
lean_inc(v_config_353_);
return v_config_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___boxed(lean_object* v_p_354_, lean_object* v_self_355_, lean_object* v_h_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lake_PConfigDecl_opaqueTargetConfig(v_p_354_, v_self_355_, v_h_356_);
lean_dec_ref(v_self_355_);
lean_dec(v_p_354_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg(lean_object* v_self_358_){
_start:
{
lean_object* v_config_359_; 
v_config_359_ = lean_ctor_get(v_self_358_, 3);
lean_inc(v_config_359_);
return v_config_359_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object* v_self_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lake_NConfigDecl_opaqueTargetConfig___redArg(v_self_360_);
lean_dec_ref(v_self_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig(lean_object* v_p_362_, lean_object* v_n_363_, lean_object* v_self_364_, lean_object* v_h_365_){
_start:
{
lean_object* v_config_366_; 
v_config_366_ = lean_ctor_get(v_self_364_, 3);
lean_inc(v_config_366_);
return v_config_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___boxed(lean_object* v_p_367_, lean_object* v_n_368_, lean_object* v_self_369_, lean_object* v_h_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lake_NConfigDecl_opaqueTargetConfig(v_p_367_, v_n_368_, v_self_369_, v_h_370_);
lean_dec_ref(v_self_369_);
lean_dec(v_n_368_);
lean_dec(v_p_367_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object* v_self_372_){
_start:
{
lean_object* v_kind_373_; lean_object* v_config_374_; uint8_t v___x_375_; 
v_kind_373_ = lean_ctor_get(v_self_372_, 2);
v_config_374_ = lean_ctor_get(v_self_372_, 3);
v___x_375_ = l_Lean_Name_isAnonymous(v_kind_373_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
lean_inc(v_config_374_);
v___x_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_377_, 0, v_config_374_);
return v___x_377_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object* v_self_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_378_);
lean_dec_ref(v_self_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f(lean_object* v_p_380_, lean_object* v_self_381_){
_start:
{
lean_object* v_kind_382_; lean_object* v_config_383_; uint8_t v___x_384_; 
v_kind_382_ = lean_ctor_get(v_self_381_, 2);
v_config_383_ = lean_ctor_get(v_self_381_, 3);
v___x_384_ = l_Lean_Name_isAnonymous(v_kind_382_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
else
{
lean_object* v___x_386_; 
lean_inc(v_config_383_);
v___x_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_386_, 0, v_config_383_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object* v_p_387_, lean_object* v_self_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f(v_p_387_, v_self_388_);
lean_dec_ref(v_self_388_);
lean_dec(v_p_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object* v_self_390_){
_start:
{
lean_object* v_kind_391_; lean_object* v_config_392_; uint8_t v___x_393_; 
v_kind_391_ = lean_ctor_get(v_self_390_, 2);
v_config_392_ = lean_ctor_get(v_self_390_, 3);
v___x_393_ = l_Lean_Name_isAnonymous(v_kind_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_box(0);
return v___x_394_;
}
else
{
lean_object* v___x_395_; 
lean_inc(v_config_392_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_config_392_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object* v_self_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_396_);
lean_dec_ref(v_self_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f(lean_object* v_p_398_, lean_object* v_n_399_, lean_object* v_self_400_){
_start:
{
lean_object* v_kind_401_; lean_object* v_config_402_; uint8_t v___x_403_; 
v_kind_401_ = lean_ctor_get(v_self_400_, 2);
v_config_402_ = lean_ctor_get(v_self_400_, 3);
v___x_403_ = l_Lean_Name_isAnonymous(v_kind_401_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; 
v___x_404_ = lean_box(0);
return v___x_404_;
}
else
{
lean_object* v___x_405_; 
lean_inc(v_config_402_);
v___x_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_405_, 0, v_config_402_);
return v___x_405_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object* v_p_406_, lean_object* v_n_407_, lean_object* v_self_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f(v_p_406_, v_n_407_, v_self_408_);
lean_dec_ref(v_self_408_);
lean_dec(v_n_407_);
lean_dec(v_p_406_);
return v_res_409_;
}
}
lean_object* runtime_initialize_Lake_Config_Opaque(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanLibConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanExeConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ExternLibConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InputFileConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_ConfigDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanLibConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanExeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_ExternLibConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_InputFileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_ConfigDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lake_PConfigDecl_pkg__eq___autoParam = _init_l_Lake_PConfigDecl_pkg__eq___autoParam();
lean_mark_persistent(l_Lake_PConfigDecl_pkg__eq___autoParam);
l_Lake_NConfigDecl_name__eq___autoParam = _init_l_Lake_NConfigDecl_name__eq___autoParam();
lean_mark_persistent(l_Lake_NConfigDecl_name__eq___autoParam);
l_Lake_KConfigDecl_kind__eq___autoParam = _init_l_Lake_KConfigDecl_kind__eq___autoParam();
lean_mark_persistent(l_Lake_KConfigDecl_kind__eq___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_Opaque(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanLibConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_LeanExeConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_ExternLibConfig(uint8_t builtin);
lean_object* initialize_Lake_Config_InputFileConfig(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_ConfigDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanLibConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_LeanExeConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_ExternLibConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_InputFileConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_ConfigDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_ConfigDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_ConfigDecl(builtin);
}
#ifdef __cplusplus
}
#endif

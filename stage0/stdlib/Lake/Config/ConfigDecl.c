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
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___closed__0 = (const lean_object*)&l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg();
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___lam__0(lean_object* v_x_74_){
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
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___lam__0___boxed(lean_object* v_x_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___lam__0(v_x_78_);
lean_dec_ref(v_x_78_);
return v_res_79_;
}
}
lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg(){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = ((lean_object*)(l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___closed__0));
return v___f_82_;
}
}
LEAN_EXPORT void l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_83_;
v_res_83_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg();
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___boxed(lean_object* v___dummy_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey(lean_object* v_k_86_){
_start:
{
lean_object* v___f_87_; 
v___f_87_ = ((lean_object*)(l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___closed__0));
return v___f_87_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___boxed(lean_object* v_k_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey(v_k_88_);
lean_dec(v_k_88_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg(lean_object* v_self_90_){
_start:
{
lean_object* v_config_91_; 
v_config_91_ = lean_ctor_get(v_self_90_, 3);
lean_inc(v_config_91_);
return v_config_91_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg___boxed(lean_object* v_self_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lake_PConfigDecl_config_x27___redArg(v_self_92_);
lean_dec_ref(v_self_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27(lean_object* v_p_94_, lean_object* v_self_95_){
_start:
{
lean_object* v_config_96_; 
v_config_96_ = lean_ctor_get(v_self_95_, 3);
lean_inc(v_config_96_);
return v_config_96_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___boxed(lean_object* v_p_97_, lean_object* v_self_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lake_PConfigDecl_config_x27(v_p_97_, v_self_98_);
lean_dec_ref(v_self_98_);
lean_dec(v_p_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg(lean_object* v_self_100_){
_start:
{
lean_object* v_config_101_; 
v_config_101_ = lean_ctor_get(v_self_100_, 3);
lean_inc(v_config_101_);
return v_config_101_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg___boxed(lean_object* v_self_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lake_NConfigDecl_config_x27___redArg(v_self_102_);
lean_dec_ref(v_self_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27(lean_object* v_p_104_, lean_object* v_n_105_, lean_object* v_self_106_){
_start:
{
lean_object* v_config_107_; 
v_config_107_ = lean_ctor_get(v_self_106_, 3);
lean_inc(v_config_107_);
return v_config_107_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___boxed(lean_object* v_p_108_, lean_object* v_n_109_, lean_object* v_self_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lake_NConfigDecl_config_x27(v_p_108_, v_n_109_, v_self_110_);
lean_dec_ref(v_self_110_);
lean_dec(v_n_109_);
lean_dec(v_p_108_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f(lean_object* v_kind_112_, lean_object* v_self_113_){
_start:
{
lean_object* v_kind_114_; lean_object* v_config_115_; uint8_t v___x_116_; 
v_kind_114_ = lean_ctor_get(v_self_113_, 2);
v_config_115_ = lean_ctor_get(v_self_113_, 3);
v___x_116_ = lean_name_eq(v_kind_114_, v_kind_112_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
else
{
lean_object* v___x_118_; 
lean_inc(v_config_115_);
v___x_118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_118_, 0, v_config_115_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f___boxed(lean_object* v_kind_119_, lean_object* v_self_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lake_ConfigDecl_config_x3f(v_kind_119_, v_self_120_);
lean_dec_ref(v_self_120_);
lean_dec(v_kind_119_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg(lean_object* v_kind_122_, lean_object* v_self_123_){
_start:
{
lean_object* v_kind_124_; lean_object* v_config_125_; uint8_t v___x_126_; 
v_kind_124_ = lean_ctor_get(v_self_123_, 2);
v_config_125_ = lean_ctor_get(v_self_123_, 3);
v___x_126_ = lean_name_eq(v_kind_124_, v_kind_122_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_box(0);
return v___x_127_;
}
else
{
lean_object* v___x_128_; 
lean_inc(v_config_125_);
v___x_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_128_, 0, v_config_125_);
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg___boxed(lean_object* v_kind_129_, lean_object* v_self_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lake_PConfigDecl_config_x3f___redArg(v_kind_129_, v_self_130_);
lean_dec_ref(v_self_130_);
lean_dec(v_kind_129_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f(lean_object* v_p_132_, lean_object* v_kind_133_, lean_object* v_self_134_){
_start:
{
lean_object* v_kind_135_; lean_object* v_config_136_; uint8_t v___x_137_; 
v_kind_135_ = lean_ctor_get(v_self_134_, 2);
v_config_136_ = lean_ctor_get(v_self_134_, 3);
v___x_137_ = lean_name_eq(v_kind_135_, v_kind_133_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
else
{
lean_object* v___x_139_; 
lean_inc(v_config_136_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_config_136_);
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___boxed(lean_object* v_p_140_, lean_object* v_kind_141_, lean_object* v_self_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lake_PConfigDecl_config_x3f(v_p_140_, v_kind_141_, v_self_142_);
lean_dec_ref(v_self_142_);
lean_dec(v_kind_141_);
lean_dec(v_p_140_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg(lean_object* v_kind_144_, lean_object* v_self_145_){
_start:
{
lean_object* v_kind_146_; lean_object* v_config_147_; uint8_t v___x_148_; 
v_kind_146_ = lean_ctor_get(v_self_145_, 2);
v_config_147_ = lean_ctor_get(v_self_145_, 3);
v___x_148_ = lean_name_eq(v_kind_146_, v_kind_144_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; 
v___x_149_ = lean_box(0);
return v___x_149_;
}
else
{
lean_object* v___x_150_; 
lean_inc(v_config_147_);
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v_config_147_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg___boxed(lean_object* v_kind_151_, lean_object* v_self_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lake_NConfigDecl_config_x3f___redArg(v_kind_151_, v_self_152_);
lean_dec_ref(v_self_152_);
lean_dec(v_kind_151_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f(lean_object* v_p_154_, lean_object* v_n_155_, lean_object* v_kind_156_, lean_object* v_self_157_){
_start:
{
lean_object* v_kind_158_; lean_object* v_config_159_; uint8_t v___x_160_; 
v_kind_158_ = lean_ctor_get(v_self_157_, 2);
v_config_159_ = lean_ctor_get(v_self_157_, 3);
v___x_160_ = lean_name_eq(v_kind_158_, v_kind_156_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_box(0);
return v___x_161_;
}
else
{
lean_object* v___x_162_; 
lean_inc(v_config_159_);
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v_config_159_);
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___boxed(lean_object* v_p_163_, lean_object* v_n_164_, lean_object* v_kind_165_, lean_object* v_self_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lake_NConfigDecl_config_x3f(v_p_163_, v_n_164_, v_kind_165_, v_self_166_);
lean_dec_ref(v_self_166_);
lean_dec(v_kind_165_);
lean_dec(v_n_164_);
lean_dec(v_p_163_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f(lean_object* v_self_171_){
_start:
{
lean_object* v_kind_172_; lean_object* v_config_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_kind_172_ = lean_ctor_get(v_self_171_, 2);
v_config_173_ = lean_ctor_get(v_self_171_, 3);
v___x_174_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_175_ = lean_name_eq(v_kind_172_, v___x_174_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v___x_177_; 
lean_inc(v_config_173_);
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v_config_173_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f___boxed(lean_object* v_self_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lake_ConfigDecl_leanLibConfig_x3f(v_self_178_);
lean_dec_ref(v_self_178_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(lean_object* v_self_180_){
_start:
{
lean_object* v_kind_181_; lean_object* v_config_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_kind_181_ = lean_ctor_get(v_self_180_, 2);
v_config_182_ = lean_ctor_get(v_self_180_, 3);
v___x_183_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_184_ = lean_name_eq(v_kind_181_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_box(0);
return v___x_185_;
}
else
{
lean_object* v___x_186_; 
lean_inc(v_config_182_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v_config_182_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg___boxed(lean_object* v_self_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(v_self_187_);
lean_dec_ref(v_self_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f(lean_object* v_p_189_, lean_object* v_n_190_, lean_object* v_self_191_){
_start:
{
lean_object* v_kind_192_; lean_object* v_config_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v_kind_192_ = lean_ctor_get(v_self_191_, 2);
v_config_193_ = lean_ctor_get(v_self_191_, 3);
v___x_194_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_195_ = lean_name_eq(v_kind_192_, v___x_194_);
if (v___x_195_ == 0)
{
lean_object* v___x_196_; 
v___x_196_ = lean_box(0);
return v___x_196_;
}
else
{
lean_object* v___x_197_; 
lean_inc(v_config_193_);
v___x_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_197_, 0, v_config_193_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___boxed(lean_object* v_p_198_, lean_object* v_n_199_, lean_object* v_self_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_NConfigDecl_leanLibConfig_x3f(v_p_198_, v_n_199_, v_self_200_);
lean_dec_ref(v_self_200_);
lean_dec(v_n_199_);
lean_dec(v_p_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f(lean_object* v_self_202_){
_start:
{
lean_object* v_kind_203_; lean_object* v_config_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v_kind_203_ = lean_ctor_get(v_self_202_, 2);
v_config_204_ = lean_ctor_get(v_self_202_, 3);
v___x_205_ = l_Lake_LeanExe_keyword;
v___x_206_ = lean_name_eq(v_kind_203_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(0);
return v___x_207_;
}
else
{
lean_object* v___x_208_; 
lean_inc(v_config_204_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v_config_204_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f___boxed(lean_object* v_self_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lake_ConfigDecl_leanExeConfig_x3f(v_self_209_);
lean_dec_ref(v_self_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(lean_object* v_self_211_){
_start:
{
lean_object* v_kind_212_; lean_object* v_config_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_kind_212_ = lean_ctor_get(v_self_211_, 2);
v_config_213_ = lean_ctor_get(v_self_211_, 3);
v___x_214_ = l_Lake_LeanExe_keyword;
v___x_215_ = lean_name_eq(v_kind_212_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_box(0);
return v___x_216_;
}
else
{
lean_object* v___x_217_; 
lean_inc(v_config_213_);
v___x_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_217_, 0, v_config_213_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg___boxed(lean_object* v_self_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(v_self_218_);
lean_dec_ref(v_self_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f(lean_object* v_p_220_, lean_object* v_n_221_, lean_object* v_self_222_){
_start:
{
lean_object* v_kind_223_; lean_object* v_config_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_kind_223_ = lean_ctor_get(v_self_222_, 2);
v_config_224_ = lean_ctor_get(v_self_222_, 3);
v___x_225_ = l_Lake_LeanExe_keyword;
v___x_226_ = lean_name_eq(v_kind_223_, v___x_225_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; 
v___x_227_ = lean_box(0);
return v___x_227_;
}
else
{
lean_object* v___x_228_; 
lean_inc(v_config_224_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_config_224_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___boxed(lean_object* v_p_229_, lean_object* v_n_230_, lean_object* v_self_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_NConfigDecl_leanExeConfig_x3f(v_p_229_, v_n_230_, v_self_231_);
lean_dec_ref(v_self_231_);
lean_dec(v_n_230_);
lean_dec(v_p_229_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg(lean_object* v_self_233_){
_start:
{
lean_object* v_kind_234_; lean_object* v_config_235_; lean_object* v___x_236_; uint8_t v___x_237_; 
v_kind_234_ = lean_ctor_get(v_self_233_, 2);
v_config_235_ = lean_ctor_get(v_self_233_, 3);
v___x_236_ = l_Lake_ExternLib_keyword;
v___x_237_ = lean_name_eq(v_kind_234_, v___x_236_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
lean_inc(v_config_235_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v_config_235_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object* v_self_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_PConfigDecl_externLibConfig_x3f___redArg(v_self_240_);
lean_dec_ref(v_self_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f(lean_object* v_p_242_, lean_object* v_self_243_){
_start:
{
lean_object* v_kind_244_; lean_object* v_config_245_; lean_object* v___x_246_; uint8_t v___x_247_; 
v_kind_244_ = lean_ctor_get(v_self_243_, 2);
v_config_245_ = lean_ctor_get(v_self_243_, 3);
v___x_246_ = l_Lake_ExternLib_keyword;
v___x_247_ = lean_name_eq(v_kind_244_, v___x_246_);
if (v___x_247_ == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_box(0);
return v___x_248_;
}
else
{
lean_object* v___x_249_; 
lean_inc(v_config_245_);
v___x_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_249_, 0, v_config_245_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___boxed(lean_object* v_p_250_, lean_object* v_self_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_PConfigDecl_externLibConfig_x3f(v_p_250_, v_self_251_);
lean_dec_ref(v_self_251_);
lean_dec(v_p_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg(lean_object* v_self_253_){
_start:
{
lean_object* v_kind_254_; lean_object* v_config_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_kind_254_ = lean_ctor_get(v_self_253_, 2);
v_config_255_ = lean_ctor_get(v_self_253_, 3);
v___x_256_ = l_Lake_ExternLib_keyword;
v___x_257_ = lean_name_eq(v_kind_254_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_box(0);
return v___x_258_;
}
else
{
lean_object* v___x_259_; 
lean_inc(v_config_255_);
v___x_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_259_, 0, v_config_255_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object* v_self_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lake_NConfigDecl_externLibConfig_x3f___redArg(v_self_260_);
lean_dec_ref(v_self_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f(lean_object* v_p_262_, lean_object* v_n_263_, lean_object* v_self_264_){
_start:
{
lean_object* v_kind_265_; lean_object* v_config_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_kind_265_ = lean_ctor_get(v_self_264_, 2);
v_config_266_ = lean_ctor_get(v_self_264_, 3);
v___x_267_ = l_Lake_ExternLib_keyword;
v___x_268_ = lean_name_eq(v_kind_265_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_box(0);
return v___x_269_;
}
else
{
lean_object* v___x_270_; 
lean_inc(v_config_266_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_config_266_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___boxed(lean_object* v_p_271_, lean_object* v_n_272_, lean_object* v_self_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lake_NConfigDecl_externLibConfig_x3f(v_p_271_, v_n_272_, v_self_273_);
lean_dec_ref(v_self_273_);
lean_dec(v_n_272_);
lean_dec(v_p_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg(lean_object* v_kind_280_, lean_object* v_h__1_281_, lean_object* v_h__2_282_, lean_object* v_h__3_283_, lean_object* v_h__4_284_, lean_object* v_h__5_285_, lean_object* v_h__6_286_, lean_object* v_h__7_287_){
_start:
{
switch(lean_obj_tag(v_kind_280_))
{
case 1:
{
lean_object* v_pre_288_; 
lean_dec(v_h__4_284_);
v_pre_288_ = lean_ctor_get(v_kind_280_, 0);
if (lean_obj_tag(v_pre_288_) == 0)
{
lean_object* v_str_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v_str_289_ = lean_ctor_get(v_kind_280_, 1);
v___x_290_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0));
v___x_291_ = lean_string_dec_eq(v_str_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; uint8_t v___x_293_; 
lean_dec(v_h__1_281_);
v___x_292_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1));
v___x_293_ = lean_string_dec_eq(v_str_289_, v___x_292_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; uint8_t v___x_295_; 
lean_dec(v_h__2_282_);
v___x_294_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2));
v___x_295_ = lean_string_dec_eq(v_str_289_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v___x_296_; uint8_t v___x_297_; 
lean_dec(v_h__3_283_);
v___x_296_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3));
v___x_297_ = lean_string_dec_eq(v_str_289_, v___x_296_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; uint8_t v___x_299_; 
lean_dec(v_h__5_285_);
v___x_298_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4));
v___x_299_ = lean_string_dec_eq(v_str_289_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
lean_dec(v_h__6_286_);
v___x_300_ = lean_apply_7(v_h__7_287_, v_kind_280_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref_known(v_kind_280_, 2);
lean_dec(v_h__7_287_);
v___x_301_ = lean_box(0);
v___x_302_ = lean_apply_1(v_h__6_286_, v___x_301_);
return v___x_302_;
}
}
else
{
lean_object* v___x_303_; lean_object* v___x_304_; 
lean_dec_ref_known(v_kind_280_, 2);
lean_dec(v_h__7_287_);
lean_dec(v_h__6_286_);
v___x_303_ = lean_box(0);
v___x_304_ = lean_apply_1(v_h__5_285_, v___x_303_);
return v___x_304_;
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec_ref_known(v_kind_280_, 2);
lean_dec(v_h__7_287_);
lean_dec(v_h__6_286_);
lean_dec(v_h__5_285_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_1(v_h__3_283_, v___x_305_);
return v___x_306_;
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec_ref_known(v_kind_280_, 2);
lean_dec(v_h__7_287_);
lean_dec(v_h__6_286_);
lean_dec(v_h__5_285_);
lean_dec(v_h__3_283_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_1(v_h__2_282_, v___x_307_);
return v___x_308_;
}
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref_known(v_kind_280_, 2);
lean_dec(v_h__7_287_);
lean_dec(v_h__6_286_);
lean_dec(v_h__5_285_);
lean_dec(v_h__3_283_);
lean_dec(v_h__2_282_);
v___x_309_ = lean_box(0);
v___x_310_ = lean_apply_1(v_h__1_281_, v___x_309_);
return v___x_310_;
}
}
else
{
lean_object* v___x_311_; 
lean_dec(v_h__6_286_);
lean_dec(v_h__5_285_);
lean_dec(v_h__3_283_);
lean_dec(v_h__2_282_);
lean_dec(v_h__1_281_);
v___x_311_ = lean_apply_7(v_h__7_287_, v_kind_280_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_311_;
}
}
case 0:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v_h__7_287_);
lean_dec(v_h__6_286_);
lean_dec(v_h__5_285_);
lean_dec(v_h__3_283_);
lean_dec(v_h__2_282_);
lean_dec(v_h__1_281_);
v___x_312_ = lean_box(0);
v___x_313_ = lean_apply_1(v_h__4_284_, v___x_312_);
return v___x_313_;
}
default: 
{
lean_object* v___x_314_; 
lean_dec(v_h__6_286_);
lean_dec(v_h__5_285_);
lean_dec(v_h__4_284_);
lean_dec(v_h__3_283_);
lean_dec(v_h__2_282_);
lean_dec(v_h__1_281_);
v___x_314_ = lean_apply_7(v_h__7_287_, v_kind_280_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter(lean_object* v_motive_315_, lean_object* v_kind_316_, lean_object* v_h__1_317_, lean_object* v_h__2_318_, lean_object* v_h__3_319_, lean_object* v_h__4_320_, lean_object* v_h__5_321_, lean_object* v_h__6_322_, lean_object* v_h__7_323_){
_start:
{
switch(lean_obj_tag(v_kind_316_))
{
case 1:
{
lean_object* v_pre_324_; 
lean_dec(v_h__4_320_);
v_pre_324_ = lean_ctor_get(v_kind_316_, 0);
if (lean_obj_tag(v_pre_324_) == 0)
{
lean_object* v_str_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_str_325_ = lean_ctor_get(v_kind_316_, 1);
v___x_326_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0));
v___x_327_ = lean_string_dec_eq(v_str_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; uint8_t v___x_329_; 
lean_dec(v_h__1_317_);
v___x_328_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1));
v___x_329_ = lean_string_dec_eq(v_str_325_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; uint8_t v___x_331_; 
lean_dec(v_h__2_318_);
v___x_330_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2));
v___x_331_ = lean_string_dec_eq(v_str_325_, v___x_330_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; uint8_t v___x_333_; 
lean_dec(v_h__3_319_);
v___x_332_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3));
v___x_333_ = lean_string_dec_eq(v_str_325_, v___x_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; uint8_t v___x_335_; 
lean_dec(v_h__5_321_);
v___x_334_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4));
v___x_335_ = lean_string_dec_eq(v_str_325_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; 
lean_dec(v_h__6_322_);
v___x_336_ = lean_apply_7(v_h__7_323_, v_kind_316_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec_ref_known(v_kind_316_, 2);
lean_dec(v_h__7_323_);
v___x_337_ = lean_box(0);
v___x_338_ = lean_apply_1(v_h__6_322_, v___x_337_);
return v___x_338_;
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec_ref_known(v_kind_316_, 2);
lean_dec(v_h__7_323_);
lean_dec(v_h__6_322_);
v___x_339_ = lean_box(0);
v___x_340_ = lean_apply_1(v_h__5_321_, v___x_339_);
return v___x_340_;
}
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; 
lean_dec_ref_known(v_kind_316_, 2);
lean_dec(v_h__7_323_);
lean_dec(v_h__6_322_);
lean_dec(v_h__5_321_);
v___x_341_ = lean_box(0);
v___x_342_ = lean_apply_1(v_h__3_319_, v___x_341_);
return v___x_342_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec_ref_known(v_kind_316_, 2);
lean_dec(v_h__7_323_);
lean_dec(v_h__6_322_);
lean_dec(v_h__5_321_);
lean_dec(v_h__3_319_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_apply_1(v_h__2_318_, v___x_343_);
return v___x_344_;
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec_ref_known(v_kind_316_, 2);
lean_dec(v_h__7_323_);
lean_dec(v_h__6_322_);
lean_dec(v_h__5_321_);
lean_dec(v_h__3_319_);
lean_dec(v_h__2_318_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_apply_1(v_h__1_317_, v___x_345_);
return v___x_346_;
}
}
else
{
lean_object* v___x_347_; 
lean_dec(v_h__6_322_);
lean_dec(v_h__5_321_);
lean_dec(v_h__3_319_);
lean_dec(v_h__2_318_);
lean_dec(v_h__1_317_);
v___x_347_ = lean_apply_7(v_h__7_323_, v_kind_316_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_347_;
}
}
case 0:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_h__7_323_);
lean_dec(v_h__6_322_);
lean_dec(v_h__5_321_);
lean_dec(v_h__3_319_);
lean_dec(v_h__2_318_);
lean_dec(v_h__1_317_);
v___x_348_ = lean_box(0);
v___x_349_ = lean_apply_1(v_h__4_320_, v___x_348_);
return v___x_349_;
}
default: 
{
lean_object* v___x_350_; 
lean_dec(v_h__6_322_);
lean_dec(v_h__5_321_);
lean_dec(v_h__4_320_);
lean_dec(v_h__3_319_);
lean_dec(v_h__2_318_);
lean_dec(v_h__1_317_);
v___x_350_ = lean_apply_7(v_h__7_323_, v_kind_316_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg(lean_object* v_self_351_){
_start:
{
lean_object* v_config_352_; 
v_config_352_ = lean_ctor_get(v_self_351_, 3);
lean_inc(v_config_352_);
return v_config_352_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object* v_self_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lake_PConfigDecl_opaqueTargetConfig___redArg(v_self_353_);
lean_dec_ref(v_self_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig(lean_object* v_p_355_, lean_object* v_self_356_, lean_object* v_h_357_){
_start:
{
lean_object* v_config_358_; 
v_config_358_ = lean_ctor_get(v_self_356_, 3);
lean_inc(v_config_358_);
return v_config_358_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___boxed(lean_object* v_p_359_, lean_object* v_self_360_, lean_object* v_h_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lake_PConfigDecl_opaqueTargetConfig(v_p_359_, v_self_360_, v_h_361_);
lean_dec_ref(v_self_360_);
lean_dec(v_p_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg(lean_object* v_self_363_){
_start:
{
lean_object* v_config_364_; 
v_config_364_ = lean_ctor_get(v_self_363_, 3);
lean_inc(v_config_364_);
return v_config_364_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object* v_self_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lake_NConfigDecl_opaqueTargetConfig___redArg(v_self_365_);
lean_dec_ref(v_self_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig(lean_object* v_p_367_, lean_object* v_n_368_, lean_object* v_self_369_, lean_object* v_h_370_){
_start:
{
lean_object* v_config_371_; 
v_config_371_ = lean_ctor_get(v_self_369_, 3);
lean_inc(v_config_371_);
return v_config_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___boxed(lean_object* v_p_372_, lean_object* v_n_373_, lean_object* v_self_374_, lean_object* v_h_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lake_NConfigDecl_opaqueTargetConfig(v_p_372_, v_n_373_, v_self_374_, v_h_375_);
lean_dec_ref(v_self_374_);
lean_dec(v_n_373_);
lean_dec(v_p_372_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object* v_self_377_){
_start:
{
lean_object* v_kind_378_; lean_object* v_config_379_; uint8_t v___x_380_; 
v_kind_378_ = lean_ctor_get(v_self_377_, 2);
v_config_379_ = lean_ctor_get(v_self_377_, 3);
v___x_380_ = l_Lean_Name_isAnonymous(v_kind_378_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
else
{
lean_object* v___x_382_; 
lean_inc(v_config_379_);
v___x_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_382_, 0, v_config_379_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object* v_self_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_383_);
lean_dec_ref(v_self_383_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f(lean_object* v_p_385_, lean_object* v_self_386_){
_start:
{
lean_object* v_kind_387_; lean_object* v_config_388_; uint8_t v___x_389_; 
v_kind_387_ = lean_ctor_get(v_self_386_, 2);
v_config_388_ = lean_ctor_get(v_self_386_, 3);
v___x_389_ = l_Lean_Name_isAnonymous(v_kind_387_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; 
v___x_390_ = lean_box(0);
return v___x_390_;
}
else
{
lean_object* v___x_391_; 
lean_inc(v_config_388_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v_config_388_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object* v_p_392_, lean_object* v_self_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f(v_p_392_, v_self_393_);
lean_dec_ref(v_self_393_);
lean_dec(v_p_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object* v_self_395_){
_start:
{
lean_object* v_kind_396_; lean_object* v_config_397_; uint8_t v___x_398_; 
v_kind_396_ = lean_ctor_get(v_self_395_, 2);
v_config_397_ = lean_ctor_get(v_self_395_, 3);
v___x_398_ = l_Lean_Name_isAnonymous(v_kind_396_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_box(0);
return v___x_399_;
}
else
{
lean_object* v___x_400_; 
lean_inc(v_config_397_);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_config_397_);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object* v_self_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_401_);
lean_dec_ref(v_self_401_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f(lean_object* v_p_403_, lean_object* v_n_404_, lean_object* v_self_405_){
_start:
{
lean_object* v_kind_406_; lean_object* v_config_407_; uint8_t v___x_408_; 
v_kind_406_ = lean_ctor_get(v_self_405_, 2);
v_config_407_ = lean_ctor_get(v_self_405_, 3);
v___x_408_ = l_Lean_Name_isAnonymous(v_kind_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
v___x_409_ = lean_box(0);
return v___x_409_;
}
else
{
lean_object* v___x_410_; 
lean_inc(v_config_407_);
v___x_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_410_, 0, v_config_407_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object* v_p_411_, lean_object* v_n_412_, lean_object* v_self_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f(v_p_411_, v_n_412_, v_self_413_);
lean_dec_ref(v_self_413_);
lean_dec(v_n_412_);
lean_dec(v_p_411_);
return v_res_414_;
}
}
lean_object* runtime_initialize_Lake_Config_Opaque(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanLibConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_LeanExeConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_ExternLibConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_InputFileConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_ConfigDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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

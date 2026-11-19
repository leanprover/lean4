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
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg(){
_start:
{
lean_object* v___f_82_; 
v___f_82_ = ((lean_object*)(l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___closed__0));
return v___f_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___boxed(lean_object* v___dummy_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg();
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey(lean_object* v_k_85_){
_start:
{
lean_object* v___f_86_; 
v___f_86_ = ((lean_object*)(l_Lake_instCoeOutKConfigDeclPartialBuildKey___redArg___closed__0));
return v___f_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeOutKConfigDeclPartialBuildKey___boxed(lean_object* v_k_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lake_instCoeOutKConfigDeclPartialBuildKey(v_k_87_);
lean_dec(v_k_87_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg(lean_object* v_self_89_){
_start:
{
lean_object* v_config_90_; 
v_config_90_ = lean_ctor_get(v_self_89_, 3);
lean_inc(v_config_90_);
return v_config_90_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___redArg___boxed(lean_object* v_self_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lake_PConfigDecl_config_x27___redArg(v_self_91_);
lean_dec_ref(v_self_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27(lean_object* v_p_93_, lean_object* v_self_94_){
_start:
{
lean_object* v_config_95_; 
v_config_95_ = lean_ctor_get(v_self_94_, 3);
lean_inc(v_config_95_);
return v_config_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x27___boxed(lean_object* v_p_96_, lean_object* v_self_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lake_PConfigDecl_config_x27(v_p_96_, v_self_97_);
lean_dec_ref(v_self_97_);
lean_dec(v_p_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg(lean_object* v_self_99_){
_start:
{
lean_object* v_config_100_; 
v_config_100_ = lean_ctor_get(v_self_99_, 3);
lean_inc(v_config_100_);
return v_config_100_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___redArg___boxed(lean_object* v_self_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lake_NConfigDecl_config_x27___redArg(v_self_101_);
lean_dec_ref(v_self_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27(lean_object* v_p_103_, lean_object* v_n_104_, lean_object* v_self_105_){
_start:
{
lean_object* v_config_106_; 
v_config_106_ = lean_ctor_get(v_self_105_, 3);
lean_inc(v_config_106_);
return v_config_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x27___boxed(lean_object* v_p_107_, lean_object* v_n_108_, lean_object* v_self_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lake_NConfigDecl_config_x27(v_p_107_, v_n_108_, v_self_109_);
lean_dec_ref(v_self_109_);
lean_dec(v_n_108_);
lean_dec(v_p_107_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f(lean_object* v_kind_111_, lean_object* v_self_112_){
_start:
{
lean_object* v_kind_113_; lean_object* v_config_114_; uint8_t v___x_115_; 
v_kind_113_ = lean_ctor_get(v_self_112_, 2);
v_config_114_ = lean_ctor_get(v_self_112_, 3);
v___x_115_ = lean_name_eq(v_kind_113_, v_kind_111_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v___x_117_; 
lean_inc(v_config_114_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v_config_114_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_config_x3f___boxed(lean_object* v_kind_118_, lean_object* v_self_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lake_ConfigDecl_config_x3f(v_kind_118_, v_self_119_);
lean_dec_ref(v_self_119_);
lean_dec(v_kind_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg(lean_object* v_kind_121_, lean_object* v_self_122_){
_start:
{
lean_object* v_kind_123_; lean_object* v_config_124_; uint8_t v___x_125_; 
v_kind_123_ = lean_ctor_get(v_self_122_, 2);
v_config_124_ = lean_ctor_get(v_self_122_, 3);
v___x_125_ = lean_name_eq(v_kind_123_, v_kind_121_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v___x_127_; 
lean_inc(v_config_124_);
v___x_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_127_, 0, v_config_124_);
return v___x_127_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___redArg___boxed(lean_object* v_kind_128_, lean_object* v_self_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lake_PConfigDecl_config_x3f___redArg(v_kind_128_, v_self_129_);
lean_dec_ref(v_self_129_);
lean_dec(v_kind_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f(lean_object* v_p_131_, lean_object* v_kind_132_, lean_object* v_self_133_){
_start:
{
lean_object* v_kind_134_; lean_object* v_config_135_; uint8_t v___x_136_; 
v_kind_134_ = lean_ctor_get(v_self_133_, 2);
v_config_135_ = lean_ctor_get(v_self_133_, 3);
v___x_136_ = lean_name_eq(v_kind_134_, v_kind_132_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_box(0);
return v___x_137_;
}
else
{
lean_object* v___x_138_; 
lean_inc(v_config_135_);
v___x_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_138_, 0, v_config_135_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_config_x3f___boxed(lean_object* v_p_139_, lean_object* v_kind_140_, lean_object* v_self_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lake_PConfigDecl_config_x3f(v_p_139_, v_kind_140_, v_self_141_);
lean_dec_ref(v_self_141_);
lean_dec(v_kind_140_);
lean_dec(v_p_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg(lean_object* v_kind_143_, lean_object* v_self_144_){
_start:
{
lean_object* v_kind_145_; lean_object* v_config_146_; uint8_t v___x_147_; 
v_kind_145_ = lean_ctor_get(v_self_144_, 2);
v_config_146_ = lean_ctor_get(v_self_144_, 3);
v___x_147_ = lean_name_eq(v_kind_145_, v_kind_143_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; 
v___x_148_ = lean_box(0);
return v___x_148_;
}
else
{
lean_object* v___x_149_; 
lean_inc(v_config_146_);
v___x_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_149_, 0, v_config_146_);
return v___x_149_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___redArg___boxed(lean_object* v_kind_150_, lean_object* v_self_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lake_NConfigDecl_config_x3f___redArg(v_kind_150_, v_self_151_);
lean_dec_ref(v_self_151_);
lean_dec(v_kind_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f(lean_object* v_p_153_, lean_object* v_n_154_, lean_object* v_kind_155_, lean_object* v_self_156_){
_start:
{
lean_object* v_kind_157_; lean_object* v_config_158_; uint8_t v___x_159_; 
v_kind_157_ = lean_ctor_get(v_self_156_, 2);
v_config_158_ = lean_ctor_get(v_self_156_, 3);
v___x_159_ = lean_name_eq(v_kind_157_, v_kind_155_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; 
v___x_160_ = lean_box(0);
return v___x_160_;
}
else
{
lean_object* v___x_161_; 
lean_inc(v_config_158_);
v___x_161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_161_, 0, v_config_158_);
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_config_x3f___boxed(lean_object* v_p_162_, lean_object* v_n_163_, lean_object* v_kind_164_, lean_object* v_self_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lake_NConfigDecl_config_x3f(v_p_162_, v_n_163_, v_kind_164_, v_self_165_);
lean_dec_ref(v_self_165_);
lean_dec(v_kind_164_);
lean_dec(v_n_163_);
lean_dec(v_p_162_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f(lean_object* v_self_170_){
_start:
{
lean_object* v_kind_171_; lean_object* v_config_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_kind_171_ = lean_ctor_get(v_self_170_, 2);
v_config_172_ = lean_ctor_get(v_self_170_, 3);
v___x_173_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_174_ = lean_name_eq(v_kind_171_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; 
v___x_175_ = lean_box(0);
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
lean_inc(v_config_172_);
v___x_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_176_, 0, v_config_172_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanLibConfig_x3f___boxed(lean_object* v_self_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lake_ConfigDecl_leanLibConfig_x3f(v_self_177_);
lean_dec_ref(v_self_177_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(lean_object* v_self_179_){
_start:
{
lean_object* v_kind_180_; lean_object* v_config_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_kind_180_ = lean_ctor_get(v_self_179_, 2);
v_config_181_ = lean_ctor_get(v_self_179_, 3);
v___x_182_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_183_ = lean_name_eq(v_kind_180_, v___x_182_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
else
{
lean_object* v___x_185_; 
lean_inc(v_config_181_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v_config_181_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___redArg___boxed(lean_object* v_self_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lake_NConfigDecl_leanLibConfig_x3f___redArg(v_self_186_);
lean_dec_ref(v_self_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f(lean_object* v_p_188_, lean_object* v_n_189_, lean_object* v_self_190_){
_start:
{
lean_object* v_kind_191_; lean_object* v_config_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_kind_191_ = lean_ctor_get(v_self_190_, 2);
v_config_192_ = lean_ctor_get(v_self_190_, 3);
v___x_193_ = ((lean_object*)(l_Lake_ConfigDecl_leanLibConfig_x3f___closed__1));
v___x_194_ = lean_name_eq(v_kind_191_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v___x_196_; 
lean_inc(v_config_192_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_config_192_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanLibConfig_x3f___boxed(lean_object* v_p_197_, lean_object* v_n_198_, lean_object* v_self_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_NConfigDecl_leanLibConfig_x3f(v_p_197_, v_n_198_, v_self_199_);
lean_dec_ref(v_self_199_);
lean_dec(v_n_198_);
lean_dec(v_p_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f(lean_object* v_self_201_){
_start:
{
lean_object* v_kind_202_; lean_object* v_config_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v_kind_202_ = lean_ctor_get(v_self_201_, 2);
v_config_203_ = lean_ctor_get(v_self_201_, 3);
v___x_204_ = l_Lake_LeanExe_keyword;
v___x_205_ = lean_name_eq(v_kind_202_, v___x_204_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(0);
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
lean_inc(v_config_203_);
v___x_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_207_, 0, v_config_203_);
return v___x_207_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigDecl_leanExeConfig_x3f___boxed(lean_object* v_self_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lake_ConfigDecl_leanExeConfig_x3f(v_self_208_);
lean_dec_ref(v_self_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(lean_object* v_self_210_){
_start:
{
lean_object* v_kind_211_; lean_object* v_config_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_kind_211_ = lean_ctor_get(v_self_210_, 2);
v_config_212_ = lean_ctor_get(v_self_210_, 3);
v___x_213_ = l_Lake_LeanExe_keyword;
v___x_214_ = lean_name_eq(v_kind_211_, v___x_213_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v___x_216_; 
lean_inc(v_config_212_);
v___x_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_216_, 0, v_config_212_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___redArg___boxed(lean_object* v_self_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lake_NConfigDecl_leanExeConfig_x3f___redArg(v_self_217_);
lean_dec_ref(v_self_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f(lean_object* v_p_219_, lean_object* v_n_220_, lean_object* v_self_221_){
_start:
{
lean_object* v_kind_222_; lean_object* v_config_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_kind_222_ = lean_ctor_get(v_self_221_, 2);
v_config_223_ = lean_ctor_get(v_self_221_, 3);
v___x_224_ = l_Lake_LeanExe_keyword;
v___x_225_ = lean_name_eq(v_kind_222_, v___x_224_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; 
v___x_226_ = lean_box(0);
return v___x_226_;
}
else
{
lean_object* v___x_227_; 
lean_inc(v_config_223_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v_config_223_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_leanExeConfig_x3f___boxed(lean_object* v_p_228_, lean_object* v_n_229_, lean_object* v_self_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_NConfigDecl_leanExeConfig_x3f(v_p_228_, v_n_229_, v_self_230_);
lean_dec_ref(v_self_230_);
lean_dec(v_n_229_);
lean_dec(v_p_228_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg(lean_object* v_self_232_){
_start:
{
lean_object* v_kind_233_; lean_object* v_config_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_kind_233_ = lean_ctor_get(v_self_232_, 2);
v_config_234_ = lean_ctor_get(v_self_232_, 3);
v___x_235_ = l_Lake_ExternLib_keyword;
v___x_236_ = lean_name_eq(v_kind_233_, v___x_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_box(0);
return v___x_237_;
}
else
{
lean_object* v___x_238_; 
lean_inc(v_config_234_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v_config_234_);
return v___x_238_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object* v_self_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lake_PConfigDecl_externLibConfig_x3f___redArg(v_self_239_);
lean_dec_ref(v_self_239_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f(lean_object* v_p_241_, lean_object* v_self_242_){
_start:
{
lean_object* v_kind_243_; lean_object* v_config_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_kind_243_ = lean_ctor_get(v_self_242_, 2);
v_config_244_ = lean_ctor_get(v_self_242_, 3);
v___x_245_ = l_Lake_ExternLib_keyword;
v___x_246_ = lean_name_eq(v_kind_243_, v___x_245_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_box(0);
return v___x_247_;
}
else
{
lean_object* v___x_248_; 
lean_inc(v_config_244_);
v___x_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_248_, 0, v_config_244_);
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_externLibConfig_x3f___boxed(lean_object* v_p_249_, lean_object* v_self_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lake_PConfigDecl_externLibConfig_x3f(v_p_249_, v_self_250_);
lean_dec_ref(v_self_250_);
lean_dec(v_p_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg(lean_object* v_self_252_){
_start:
{
lean_object* v_kind_253_; lean_object* v_config_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_kind_253_ = lean_ctor_get(v_self_252_, 2);
v_config_254_ = lean_ctor_get(v_self_252_, 3);
v___x_255_ = l_Lake_ExternLib_keyword;
v___x_256_ = lean_name_eq(v_kind_253_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_box(0);
return v___x_257_;
}
else
{
lean_object* v___x_258_; 
lean_inc(v_config_254_);
v___x_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_258_, 0, v_config_254_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___redArg___boxed(lean_object* v_self_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lake_NConfigDecl_externLibConfig_x3f___redArg(v_self_259_);
lean_dec_ref(v_self_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f(lean_object* v_p_261_, lean_object* v_n_262_, lean_object* v_self_263_){
_start:
{
lean_object* v_kind_264_; lean_object* v_config_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_kind_264_ = lean_ctor_get(v_self_263_, 2);
v_config_265_ = lean_ctor_get(v_self_263_, 3);
v___x_266_ = l_Lake_ExternLib_keyword;
v___x_267_ = lean_name_eq(v_kind_264_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v___x_269_; 
lean_inc(v_config_265_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_config_265_);
return v___x_269_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_externLibConfig_x3f___boxed(lean_object* v_p_270_, lean_object* v_n_271_, lean_object* v_self_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lake_NConfigDecl_externLibConfig_x3f(v_p_270_, v_n_271_, v_self_272_);
lean_dec_ref(v_self_272_);
lean_dec(v_n_271_);
lean_dec(v_p_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg(lean_object* v_kind_279_, lean_object* v_h__1_280_, lean_object* v_h__2_281_, lean_object* v_h__3_282_, lean_object* v_h__4_283_, lean_object* v_h__5_284_, lean_object* v_h__6_285_, lean_object* v_h__7_286_){
_start:
{
switch(lean_obj_tag(v_kind_279_))
{
case 1:
{
lean_object* v_pre_287_; 
lean_dec(v_h__4_283_);
v_pre_287_ = lean_ctor_get(v_kind_279_, 0);
if (lean_obj_tag(v_pre_287_) == 0)
{
lean_object* v_str_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v_str_288_ = lean_ctor_get(v_kind_279_, 1);
v___x_289_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0));
v___x_290_ = lean_string_dec_eq(v_str_288_, v___x_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; uint8_t v___x_292_; 
lean_dec(v_h__1_280_);
v___x_291_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1));
v___x_292_ = lean_string_dec_eq(v_str_288_, v___x_291_);
if (v___x_292_ == 0)
{
lean_object* v___x_293_; uint8_t v___x_294_; 
lean_dec(v_h__2_281_);
v___x_293_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2));
v___x_294_ = lean_string_dec_eq(v_str_288_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
lean_dec(v_h__3_282_);
v___x_295_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3));
v___x_296_ = lean_string_dec_eq(v_str_288_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; 
lean_dec(v_h__5_284_);
v___x_297_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4));
v___x_298_ = lean_string_dec_eq(v_str_288_, v___x_297_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
lean_dec(v_h__6_285_);
v___x_299_ = lean_apply_7(v_h__7_286_, v_kind_279_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_299_;
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec_ref_known(v_kind_279_, 2);
lean_dec(v_h__7_286_);
v___x_300_ = lean_box(0);
v___x_301_ = lean_apply_1(v_h__6_285_, v___x_300_);
return v___x_301_;
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref_known(v_kind_279_, 2);
lean_dec(v_h__7_286_);
lean_dec(v_h__6_285_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_apply_1(v_h__5_284_, v___x_302_);
return v___x_303_;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref_known(v_kind_279_, 2);
lean_dec(v_h__7_286_);
lean_dec(v_h__6_285_);
lean_dec(v_h__5_284_);
v___x_304_ = lean_box(0);
v___x_305_ = lean_apply_1(v_h__3_282_, v___x_304_);
return v___x_305_;
}
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec_ref_known(v_kind_279_, 2);
lean_dec(v_h__7_286_);
lean_dec(v_h__6_285_);
lean_dec(v_h__5_284_);
lean_dec(v_h__3_282_);
v___x_306_ = lean_box(0);
v___x_307_ = lean_apply_1(v_h__2_281_, v___x_306_);
return v___x_307_;
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec_ref_known(v_kind_279_, 2);
lean_dec(v_h__7_286_);
lean_dec(v_h__6_285_);
lean_dec(v_h__5_284_);
lean_dec(v_h__3_282_);
lean_dec(v_h__2_281_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_apply_1(v_h__1_280_, v___x_308_);
return v___x_309_;
}
}
else
{
lean_object* v___x_310_; 
lean_dec(v_h__6_285_);
lean_dec(v_h__5_284_);
lean_dec(v_h__3_282_);
lean_dec(v_h__2_281_);
lean_dec(v_h__1_280_);
v___x_310_ = lean_apply_7(v_h__7_286_, v_kind_279_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_310_;
}
}
case 0:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_h__7_286_);
lean_dec(v_h__6_285_);
lean_dec(v_h__5_284_);
lean_dec(v_h__3_282_);
lean_dec(v_h__2_281_);
lean_dec(v_h__1_280_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_apply_1(v_h__4_283_, v___x_311_);
return v___x_312_;
}
default: 
{
lean_object* v___x_313_; 
lean_dec(v_h__6_285_);
lean_dec(v_h__5_284_);
lean_dec(v_h__4_283_);
lean_dec(v_h__3_282_);
lean_dec(v_h__2_281_);
lean_dec(v_h__1_280_);
v___x_313_ = lean_apply_7(v_h__7_286_, v_kind_279_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter(lean_object* v_motive_314_, lean_object* v_kind_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_, lean_object* v_h__3_318_, lean_object* v_h__4_319_, lean_object* v_h__5_320_, lean_object* v_h__6_321_, lean_object* v_h__7_322_){
_start:
{
switch(lean_obj_tag(v_kind_315_))
{
case 1:
{
lean_object* v_pre_323_; 
lean_dec(v_h__4_319_);
v_pre_323_ = lean_ctor_get(v_kind_315_, 0);
if (lean_obj_tag(v_pre_323_) == 0)
{
lean_object* v_str_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_str_324_ = lean_ctor_get(v_kind_315_, 1);
v___x_325_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__0));
v___x_326_ = lean_string_dec_eq(v_str_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; uint8_t v___x_328_; 
lean_dec(v_h__1_316_);
v___x_327_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__1));
v___x_328_ = lean_string_dec_eq(v_str_324_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
lean_dec(v_h__2_317_);
v___x_329_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__2));
v___x_330_ = lean_string_dec_eq(v_str_324_, v___x_329_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; uint8_t v___x_332_; 
lean_dec(v_h__3_318_);
v___x_331_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__3));
v___x_332_ = lean_string_dec_eq(v_str_324_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; uint8_t v___x_334_; 
lean_dec(v_h__5_320_);
v___x_333_ = ((lean_object*)(l___private_Lake_Config_ConfigDecl_0__Lake_ConfigType_match__1_splitter___redArg___closed__4));
v___x_334_ = lean_string_dec_eq(v_str_324_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
lean_dec(v_h__6_321_);
v___x_335_ = lean_apply_7(v_h__7_322_, v_kind_315_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_335_;
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref_known(v_kind_315_, 2);
lean_dec(v_h__7_322_);
v___x_336_ = lean_box(0);
v___x_337_ = lean_apply_1(v_h__6_321_, v___x_336_);
return v___x_337_;
}
}
else
{
lean_object* v___x_338_; lean_object* v___x_339_; 
lean_dec_ref_known(v_kind_315_, 2);
lean_dec(v_h__7_322_);
lean_dec(v_h__6_321_);
v___x_338_ = lean_box(0);
v___x_339_ = lean_apply_1(v_h__5_320_, v___x_338_);
return v___x_339_;
}
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec_ref_known(v_kind_315_, 2);
lean_dec(v_h__7_322_);
lean_dec(v_h__6_321_);
lean_dec(v_h__5_320_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_apply_1(v_h__3_318_, v___x_340_);
return v___x_341_;
}
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; 
lean_dec_ref_known(v_kind_315_, 2);
lean_dec(v_h__7_322_);
lean_dec(v_h__6_321_);
lean_dec(v_h__5_320_);
lean_dec(v_h__3_318_);
v___x_342_ = lean_box(0);
v___x_343_ = lean_apply_1(v_h__2_317_, v___x_342_);
return v___x_343_;
}
}
else
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec_ref_known(v_kind_315_, 2);
lean_dec(v_h__7_322_);
lean_dec(v_h__6_321_);
lean_dec(v_h__5_320_);
lean_dec(v_h__3_318_);
lean_dec(v_h__2_317_);
v___x_344_ = lean_box(0);
v___x_345_ = lean_apply_1(v_h__1_316_, v___x_344_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec(v_h__6_321_);
lean_dec(v_h__5_320_);
lean_dec(v_h__3_318_);
lean_dec(v_h__2_317_);
lean_dec(v_h__1_316_);
v___x_346_ = lean_apply_7(v_h__7_322_, v_kind_315_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_346_;
}
}
case 0:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_h__7_322_);
lean_dec(v_h__6_321_);
lean_dec(v_h__5_320_);
lean_dec(v_h__3_318_);
lean_dec(v_h__2_317_);
lean_dec(v_h__1_316_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_apply_1(v_h__4_319_, v___x_347_);
return v___x_348_;
}
default: 
{
lean_object* v___x_349_; 
lean_dec(v_h__6_321_);
lean_dec(v_h__5_320_);
lean_dec(v_h__4_319_);
lean_dec(v_h__3_318_);
lean_dec(v_h__2_317_);
lean_dec(v_h__1_316_);
v___x_349_ = lean_apply_7(v_h__7_322_, v_kind_315_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg(lean_object* v_self_350_){
_start:
{
lean_object* v_config_351_; 
v_config_351_ = lean_ctor_get(v_self_350_, 3);
lean_inc(v_config_351_);
return v_config_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object* v_self_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lake_PConfigDecl_opaqueTargetConfig___redArg(v_self_352_);
lean_dec_ref(v_self_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig(lean_object* v_p_354_, lean_object* v_self_355_, lean_object* v_h_356_){
_start:
{
lean_object* v_config_357_; 
v_config_357_ = lean_ctor_get(v_self_355_, 3);
lean_inc(v_config_357_);
return v_config_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig___boxed(lean_object* v_p_358_, lean_object* v_self_359_, lean_object* v_h_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lake_PConfigDecl_opaqueTargetConfig(v_p_358_, v_self_359_, v_h_360_);
lean_dec_ref(v_self_359_);
lean_dec(v_p_358_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg(lean_object* v_self_362_){
_start:
{
lean_object* v_config_363_; 
v_config_363_ = lean_ctor_get(v_self_362_, 3);
lean_inc(v_config_363_);
return v_config_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___redArg___boxed(lean_object* v_self_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lake_NConfigDecl_opaqueTargetConfig___redArg(v_self_364_);
lean_dec_ref(v_self_364_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig(lean_object* v_p_366_, lean_object* v_n_367_, lean_object* v_self_368_, lean_object* v_h_369_){
_start:
{
lean_object* v_config_370_; 
v_config_370_ = lean_ctor_get(v_self_368_, 3);
lean_inc(v_config_370_);
return v_config_370_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig___boxed(lean_object* v_p_371_, lean_object* v_n_372_, lean_object* v_self_373_, lean_object* v_h_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lake_NConfigDecl_opaqueTargetConfig(v_p_371_, v_n_372_, v_self_373_, v_h_374_);
lean_dec_ref(v_self_373_);
lean_dec(v_n_372_);
lean_dec(v_p_371_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object* v_self_376_){
_start:
{
lean_object* v_kind_377_; lean_object* v_config_378_; uint8_t v___x_379_; 
v_kind_377_ = lean_ctor_get(v_self_376_, 2);
v_config_378_ = lean_ctor_get(v_self_376_, 3);
v___x_379_ = l_Lean_Name_isAnonymous(v_kind_377_);
if (v___x_379_ == 0)
{
lean_object* v___x_380_; 
v___x_380_ = lean_box(0);
return v___x_380_;
}
else
{
lean_object* v___x_381_; 
lean_inc(v_config_378_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_config_378_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object* v_self_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_382_);
lean_dec_ref(v_self_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f(lean_object* v_p_384_, lean_object* v_self_385_){
_start:
{
lean_object* v_kind_386_; lean_object* v_config_387_; uint8_t v___x_388_; 
v_kind_386_ = lean_ctor_get(v_self_385_, 2);
v_config_387_ = lean_ctor_get(v_self_385_, 3);
v___x_388_ = l_Lean_Name_isAnonymous(v_kind_386_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
lean_object* v___x_390_; 
lean_inc(v_config_387_);
v___x_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_390_, 0, v_config_387_);
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_PConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object* v_p_391_, lean_object* v_self_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lake_PConfigDecl_opaqueTargetConfig_x3f(v_p_391_, v_self_392_);
lean_dec_ref(v_self_392_);
lean_dec(v_p_391_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(lean_object* v_self_394_){
_start:
{
lean_object* v_kind_395_; lean_object* v_config_396_; uint8_t v___x_397_; 
v_kind_395_ = lean_ctor_get(v_self_394_, 2);
v_config_396_ = lean_ctor_get(v_self_394_, 3);
v___x_397_ = l_Lean_Name_isAnonymous(v_kind_395_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; 
v___x_398_ = lean_box(0);
return v___x_398_;
}
else
{
lean_object* v___x_399_; 
lean_inc(v_config_396_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_config_396_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg___boxed(lean_object* v_self_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f___redArg(v_self_400_);
lean_dec_ref(v_self_400_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f(lean_object* v_p_402_, lean_object* v_n_403_, lean_object* v_self_404_){
_start:
{
lean_object* v_kind_405_; lean_object* v_config_406_; uint8_t v___x_407_; 
v_kind_405_ = lean_ctor_get(v_self_404_, 2);
v_config_406_ = lean_ctor_get(v_self_404_, 3);
v___x_407_ = l_Lean_Name_isAnonymous(v_kind_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
v___x_408_ = lean_box(0);
return v___x_408_;
}
else
{
lean_object* v___x_409_; 
lean_inc(v_config_406_);
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_config_406_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_NConfigDecl_opaqueTargetConfig_x3f___boxed(lean_object* v_p_410_, lean_object* v_n_411_, lean_object* v_self_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lake_NConfigDecl_opaqueTargetConfig_x3f(v_p_410_, v_n_411_, v_self_412_);
lean_dec_ref(v_self_412_);
lean_dec(v_n_411_);
lean_dec(v_p_410_);
return v_res_413_;
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

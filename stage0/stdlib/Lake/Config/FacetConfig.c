// Lean compiler output
// Module: Lake.Config.FacetConfig
// Imports: public import Lake.Build.Fetch
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lake_instInhabitedJobState_default;
extern lean_object* l_Lake_Log_instInhabitedPos_default;
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lake_formatQuery___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0;
static lean_once_cell_t l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1;
static const lean_string_object l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2 = (const lean_object*)&l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2_value;
static lean_once_cell_t l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instInhabitedFacetConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedFacetConfig_default___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedFacetConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedFacetConfig_default___closed__0_value;
static const lean_closure_object l_Lake_instInhabitedFacetConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedFacetConfig_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedFacetConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedFacetConfig_default___closed__1_value;
static const lean_ctor_object l_Lake_instInhabitedFacetConfig_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedFacetConfig_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedFacetConfig_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedFacetConfig_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedFacetConfig_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__0 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value;
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__1 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value;
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__2 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value;
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__3 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__3_value;
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__4 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__4_value;
static const lean_array_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__5 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__5_value;
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__6 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__6_value;
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__7 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__7_value;
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__8 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__8_value;
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__9 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__9_value;
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__10 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__10_value;
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__11 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__11_value;
static const lean_string_object l_Lake_KFacetConfig_kind__eq___autoParam___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__12 = (const lean_object*)&l_Lake_KFacetConfig_kind__eq___autoParam___closed__12_value;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__13;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__14;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__15;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__16;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__17;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__18;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__19;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__20;
static lean_once_cell_t l_Lake_KFacetConfig_kind__eq___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_KFacetConfig_kind__eq___autoParam___closed__21;
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_kind__eq___autoParam;
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value;
static const lean_string_object l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ModuleFacetDecl"};
static const lean_object* l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1_value;
static const lean_ctor_object l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value_aux_0),((lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(131, 42, 241, 83, 30, 238, 35, 149)}};
static const lean_object* l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2 = (const lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameModuleFacetDecl_unsafe__1 = (const lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameModuleFacetDecl = (const lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__2_value;
static const lean_string_object l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "PackageFacetDecl"};
static const lean_object* l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0_value;
static const lean_ctor_object l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value_aux_0),((lean_object*)&l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 96, 9, 238, 243, 4, 145, 208)}};
static const lean_object* l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNamePackageFacetDecl_unsafe__1 = (const lean_object*)&l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNamePackageFacetDecl = (const lean_object*)&l_Lake_instTypeNamePackageFacetDecl_unsafe__1___closed__1_value;
static const lean_string_object l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "LibraryFacetDecl"};
static const lean_object* l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0_value;
static const lean_ctor_object l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instTypeNameModuleFacetDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value_aux_0),((lean_object*)&l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 177, 142, 101, 208, 59, 154, 167)}};
static const lean_object* l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameLibraryFacetDecl_unsafe__1 = (const lean_object*)&l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameLibraryFacetDecl = (const lean_object*)&l_Lake_instTypeNameLibraryFacetDecl_unsafe__1___closed__1_value;
static lean_object* _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = l_Lake_instInhabitedJobState_default;
v___x_2_ = l_Lake_Log_instInhabitedPos_default;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0, &l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0_once, _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__0);
v___x_5_ = lean_task_pure(v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3(void){
_start:
{
uint8_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_7_ = 0;
v___x_8_ = ((lean_object*)(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2));
v___x_9_ = lean_box(0);
v___x_10_ = lean_obj_once(&l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1, &l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1_once, _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__1);
v___x_11_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
lean_ctor_set(v___x_11_, 2, v___x_8_);
lean_ctor_set_uint8(v___x_11_, sizeof(void*)*3, v___x_7_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0(lean_object* v_x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_obj_once(&l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3, &l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3_once, _init_l_Lake_instInhabitedFacetConfig_default___lam__0___closed__3);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___y_18_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__0___boxed(lean_object* v_x_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lake_instInhabitedFacetConfig_default___lam__0(v_x_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec(v___y_25_);
lean_dec(v___y_24_);
lean_dec_ref(v___y_23_);
lean_dec(v_x_22_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__1(uint8_t v_x_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = ((lean_object*)(l_Lake_instInhabitedFacetConfig_default___lam__0___closed__2));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___lam__1___boxed(lean_object* v_x_34_, lean_object* v___y_35_){
_start:
{
uint8_t v_x_528__boxed_36_; lean_object* v_res_37_; 
v_x_528__boxed_36_ = lean_unbox(v_x_34_);
v_res_37_ = l_Lake_instInhabitedFacetConfig_default___lam__1(v_x_528__boxed_36_, v___y_35_);
lean_dec(v___y_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default(lean_object* v_a_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = ((lean_object*)(l_Lake_instInhabitedFacetConfig_default___closed__2));
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig_default___boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lake_instInhabitedFacetConfig_default(v_a_47_);
lean_dec(v_a_47_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig(lean_object* v_a_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lake_instInhabitedFacetConfig_default(v_a_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedFacetConfig___boxed(lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lake_instInhabitedFacetConfig(v_a_51_);
lean_dec(v_a_51_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg(lean_object* v_name_53_){
_start:
{
lean_inc(v_name_53_);
return v_name_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___redArg___boxed(lean_object* v_name_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lake_FacetConfig_name___redArg(v_name_54_);
lean_dec(v_name_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name(lean_object* v_name_56_, lean_object* v_x_57_){
_start:
{
lean_inc(v_name_56_);
return v_name_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_name___boxed(lean_object* v_name_58_, lean_object* v_x_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lake_FacetConfig_name(v_name_58_, v_x_59_);
lean_dec_ref(v_x_59_);
lean_dec(v_name_58_);
return v_res_60_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__13(void){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__12));
v___x_89_ = l_Lean_mkAtom(v___x_88_);
return v___x_89_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__14(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__13, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__13_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__13);
v___x_91_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__5));
v___x_92_ = lean_array_push(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__15(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__14, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__14_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__14);
v___x_94_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__11));
v___x_95_ = lean_box(2);
v___x_96_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_94_);
lean_ctor_set(v___x_96_, 2, v___x_93_);
return v___x_96_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__16(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__15, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__15_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__15);
v___x_98_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__5));
v___x_99_ = lean_array_push(v___x_98_, v___x_97_);
return v___x_99_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__17(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__16, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__16_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__16);
v___x_101_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__9));
v___x_102_ = lean_box(2);
v___x_103_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_100_);
return v___x_103_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__18(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__17, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__17_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__17);
v___x_105_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__5));
v___x_106_ = lean_array_push(v___x_105_, v___x_104_);
return v___x_106_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__19(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__18, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__18_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__18);
v___x_108_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__7));
v___x_109_ = lean_box(2);
v___x_110_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_108_);
lean_ctor_set(v___x_110_, 2, v___x_107_);
return v___x_110_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__20(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__19, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__19_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__19);
v___x_112_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__5));
v___x_113_ = lean_array_push(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__21(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__20, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__20_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__20);
v___x_115_ = ((lean_object*)(l_Lake_KFacetConfig_kind__eq___autoParam___closed__4));
v___x_116_ = lean_box(2);
v___x_117_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lake_KFacetConfig_kind__eq___autoParam(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lake_KFacetConfig_kind__eq___autoParam___closed__21, &l_Lake_KFacetConfig_kind__eq___autoParam___closed__21_once, _init_l_Lake_KFacetConfig_kind__eq___autoParam___closed__21);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg(lean_object* v_self_119_){
_start:
{
lean_inc_ref(v_self_119_);
return v_self_119_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___redArg___boxed(lean_object* v_self_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lake_FacetConfig_toKind___redArg(v_self_120_);
lean_dec_ref(v_self_120_);
return v_res_121_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind(lean_object* v_name_122_, lean_object* v_kind_123_, lean_object* v_self_124_, lean_object* v_h_125_){
_start:
{
lean_inc_ref(v_self_124_);
return v_self_124_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind___boxed(lean_object* v_name_126_, lean_object* v_kind_127_, lean_object* v_self_128_, lean_object* v_h_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lake_FacetConfig_toKind(v_name_126_, v_kind_127_, v_self_128_, v_h_129_);
lean_dec_ref(v_self_128_);
lean_dec(v_kind_127_);
lean_dec(v_name_126_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg(lean_object* v_kind_131_, lean_object* v_self_132_){
_start:
{
lean_object* v_kind_133_; uint8_t v___x_134_; 
v_kind_133_ = lean_ctor_get(v_self_132_, 0);
v___x_134_ = lean_name_eq(v_kind_133_, v_kind_131_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; 
lean_dec_ref(v_self_132_);
v___x_135_ = lean_box(0);
return v___x_135_;
}
else
{
lean_object* v___x_136_; 
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v_self_132_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___redArg___boxed(lean_object* v_kind_137_, lean_object* v_self_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lake_FacetConfig_toKind_x3f___redArg(v_kind_137_, v_self_138_);
lean_dec(v_kind_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f(lean_object* v_name_140_, lean_object* v_kind_141_, lean_object* v_self_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lake_FacetConfig_toKind_x3f___redArg(v_kind_141_, v_self_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_FacetConfig_toKind_x3f___boxed(lean_object* v_name_144_, lean_object* v_kind_145_, lean_object* v_self_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lake_FacetConfig_toKind_x3f(v_name_144_, v_kind_145_, v_self_146_);
lean_dec(v_kind_145_);
lean_dec(v_name_144_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___redArg(lean_object* v_self_148_, lean_object* v_info_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_fetchFn_157_; lean_object* v___x_158_; 
v_fetchFn_157_ = lean_ctor_get(v_self_148_, 1);
lean_inc_ref(v_fetchFn_157_);
lean_dec_ref(v_self_148_);
v___x_158_ = lean_apply_8(v_fetchFn_157_, v_info_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, lean_box(0));
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___redArg___boxed(lean_object* v_self_159_, lean_object* v_info_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lake_KFacetConfig_run___redArg(v_self_159_, v_info_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run(lean_object* v_kind_169_, lean_object* v_00_u03b1_170_, lean_object* v_facet_171_, lean_object* v_00_u03b2_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_self_175_, lean_object* v_info_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_fetchFn_184_; lean_object* v___x_185_; 
v_fetchFn_184_ = lean_ctor_get(v_self_175_, 1);
lean_inc_ref(v_fetchFn_184_);
lean_dec_ref(v_self_175_);
v___x_185_ = lean_apply_8(v_fetchFn_184_, v_info_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, lean_box(0));
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_KFacetConfig_run___boxed(lean_object* v_kind_186_, lean_object* v_00_u03b1_187_, lean_object* v_facet_188_, lean_object* v_00_u03b2_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_self_192_, lean_object* v_info_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_KFacetConfig_run(v_kind_186_, v_00_u03b1_187_, v_facet_188_, v_00_u03b2_189_, v_inst_190_, v_inst_191_, v_self_192_, v_info_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_facet_188_);
lean_dec(v_kind_186_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg(lean_object* v_kind_202_, lean_object* v_inst_203_, lean_object* v_outKind_204_, lean_object* v_build_205_, uint8_t v_buildable_206_, uint8_t v_memoize_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(v___x_208_, 0, lean_box(0));
lean_closure_set(v___x_208_, 1, v_inst_203_);
v___x_209_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_209_, 0, v_kind_202_);
lean_ctor_set(v___x_209_, 1, v_build_205_);
lean_ctor_set(v___x_209_, 2, v_outKind_204_);
lean_ctor_set(v___x_209_, 3, v___x_208_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*4, v_buildable_206_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*4 + 1, v_memoize_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___redArg___boxed(lean_object* v_kind_210_, lean_object* v_inst_211_, lean_object* v_outKind_212_, lean_object* v_build_213_, lean_object* v_buildable_214_, lean_object* v_memoize_215_){
_start:
{
uint8_t v_buildable_boxed_216_; uint8_t v_memoize_boxed_217_; lean_object* v_res_218_; 
v_buildable_boxed_216_ = lean_unbox(v_buildable_214_);
v_memoize_boxed_217_ = lean_unbox(v_memoize_215_);
v_res_218_ = l_Lake_mkFacetJobConfig___redArg(v_kind_210_, v_inst_211_, v_outKind_212_, v_build_213_, v_buildable_boxed_216_, v_memoize_boxed_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig(lean_object* v_00_u03b2_219_, lean_object* v_kind_220_, lean_object* v_00_u03b1_221_, lean_object* v_facet_222_, lean_object* v_inst_223_, lean_object* v_outKind_224_, lean_object* v_i_225_, lean_object* v_o_226_, lean_object* v_build_227_, uint8_t v_buildable_228_, uint8_t v_memoize_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = lean_alloc_closure((void*)(l_Lake_formatQuery___boxed), 4, 2);
lean_closure_set(v___x_230_, 0, lean_box(0));
lean_closure_set(v___x_230_, 1, v_inst_223_);
v___x_231_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_231_, 0, v_kind_220_);
lean_ctor_set(v___x_231_, 1, v_build_227_);
lean_ctor_set(v___x_231_, 2, v_outKind_224_);
lean_ctor_set(v___x_231_, 3, v___x_230_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*4, v_buildable_228_);
lean_ctor_set_uint8(v___x_231_, sizeof(void*)*4 + 1, v_memoize_229_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_mkFacetJobConfig___boxed(lean_object* v_00_u03b2_232_, lean_object* v_kind_233_, lean_object* v_00_u03b1_234_, lean_object* v_facet_235_, lean_object* v_inst_236_, lean_object* v_outKind_237_, lean_object* v_i_238_, lean_object* v_o_239_, lean_object* v_build_240_, lean_object* v_buildable_241_, lean_object* v_memoize_242_){
_start:
{
uint8_t v_buildable_boxed_243_; uint8_t v_memoize_boxed_244_; lean_object* v_res_245_; 
v_buildable_boxed_243_ = lean_unbox(v_buildable_241_);
v_memoize_boxed_244_ = lean_unbox(v_memoize_242_);
v_res_245_ = l_Lake_mkFacetJobConfig(v_00_u03b2_232_, v_kind_233_, v_00_u03b1_234_, v_facet_235_, v_inst_236_, v_outKind_237_, v_i_238_, v_o_239_, v_build_240_, v_buildable_boxed_243_, v_memoize_boxed_244_);
lean_dec(v_facet_235_);
return v_res_245_;
}
}
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_FacetConfig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lake_KFacetConfig_kind__eq___autoParam = _init_l_Lake_KFacetConfig_kind__eq___autoParam();
lean_mark_persistent(l_Lake_KFacetConfig_kind__eq___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_FacetConfig(builtin);
}
#ifdef __cplusplus
}
#endif

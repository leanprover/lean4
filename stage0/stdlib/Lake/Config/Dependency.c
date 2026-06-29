// Lean compiler output
// Module: Lake.Config.Dependency
// Imports: public import Init.Dynamic public import Init.System.FilePath public import Init.Data.ToString.Name public import Lean.Data.NameMap.Basic public import Lake.Util.Git public import Lake.Util.Version import Init.Data.String.TakeDrop import Init.Data.ToString.Macro
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
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_VerRange_parse(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_none_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ver_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ver_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedInputVer_default;
LEAN_EXPORT lean_object* l_Lake_instInhabitedInputVer;
static const lean_string_object l_Lake_instReprInputVer_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Lake.InputVer.none"};
static const lean_object* l_Lake_instReprInputVer_repr___closed__0 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprInputVer_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInputVer_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprInputVer_repr___closed__1 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__1_value;
static lean_once_cell_t l_Lake_instReprInputVer_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInputVer_repr___closed__2;
static lean_once_cell_t l_Lake_instReprInputVer_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprInputVer_repr___closed__3;
static const lean_string_object l_Lake_instReprInputVer_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lake.InputVer.git"};
static const lean_object* l_Lake_instReprInputVer_repr___closed__4 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprInputVer_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInputVer_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprInputVer_repr___closed__5 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__5_value;
static const lean_ctor_object l_Lake_instReprInputVer_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprInputVer_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprInputVer_repr___closed__6 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__6_value;
static const lean_string_object l_Lake_instReprInputVer_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lake.InputVer.ver"};
static const lean_object* l_Lake_instReprInputVer_repr___closed__7 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__7_value;
static const lean_ctor_object l_Lake_instReprInputVer_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprInputVer_repr___closed__7_value)}};
static const lean_object* l_Lake_instReprInputVer_repr___closed__8 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__8_value;
static const lean_ctor_object l_Lake_instReprInputVer_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprInputVer_repr___closed__8_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprInputVer_repr___closed__9 = (const lean_object*)&l_Lake_instReprInputVer_repr___closed__9_value;
LEAN_EXPORT lean_object* l_Lake_instReprInputVer_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInputVer_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprInputVer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprInputVer_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprInputVer___closed__0 = (const lean_object*)&l_Lake_instReprInputVer___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprInputVer = (const lean_object*)&l_Lake_instReprInputVer___closed__0_value;
static const lean_string_object l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "git#"};
static const lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_parse(lean_object*);
static const lean_closure_object l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputVer_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0 = (const lean_object*)&l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion = (const lean_object*)&l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_InputVer_toString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedDependencySrc_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedDependencySrc_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedDependencySrc_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedDependencySrc_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDependencySrc_default = (const lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDependencySrc = (const lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "FilePath.mk "};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprDependencySrc_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lake.DependencySrc.path"};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__0 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__1 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__1_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__2 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__2_value;
static const lean_string_object l_Lake_instReprDependencySrc_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lake.DependencySrc.git"};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__3 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__3_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__3_value)}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__4 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprDependencySrc_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprDependencySrc_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instReprDependencySrc_repr___closed__5 = (const lean_object*)&l_Lake_instReprDependencySrc_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprDependencySrc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprDependencySrc_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprDependencySrc___closed__0 = (const lean_object*)&l_Lake_instReprDependencySrc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprDependencySrc = (const lean_object*)&l_Lake_instReprDependencySrc___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedDependency_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedDependency_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedDependency_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDependency_default = (const lean_object*)&l_Lake_instInhabitedDependency_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedDependency = (const lean_object*)&l_Lake_instInhabitedDependency_default___closed__0_value;
static const lean_string_object l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23_ = (const lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value;
static const lean_string_object l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Dependency"};
static const lean_object* l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23_ = (const lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value;
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value),LEAN_SCALAR_PTR_LITERAL(248, 114, 43, 207, 103, 109, 40, 59)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameDependency = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_23__value;
LEAN_EXPORT lean_object* l_Lake_Dependency_dirName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_prettyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_reservoirName(lean_object*);
static const lean_string_object l_Lake_Dependency_fullName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_Dependency_fullName___closed__0 = (const lean_object*)&l_Lake_Dependency_fullName___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object*);
static const lean_string_object l_Lake_Dependency_resolverDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Lake_Dependency_resolverDescr___closed__0 = (const lean_object*)&l_Lake_Dependency_resolverDescr___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_resolverDescr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lake_InputVer_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
{
return v_k_8_;
}
else
{
lean_object* v_rev_9_; lean_object* v___x_10_; 
v_rev_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_rev_9_);
lean_dec(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_rev_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lake_InputVer_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lake_InputVer_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_none_elim___redArg(lean_object* v_t_23_, lean_object* v_none_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lake_InputVer_ctorElim___redArg(v_t_23_, v_none_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_none_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_none_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lake_InputVer_ctorElim___redArg(v_t_27_, v_none_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_git_elim___redArg(lean_object* v_t_31_, lean_object* v_git_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lake_InputVer_ctorElim___redArg(v_t_31_, v_git_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_git_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_git_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lake_InputVer_ctorElim___redArg(v_t_35_, v_git_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ver_elim___redArg(lean_object* v_t_39_, lean_object* v_ver_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lake_InputVer_ctorElim___redArg(v_t_39_, v_ver_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ver_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_ver_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lake_InputVer_ctorElim___redArg(v_t_43_, v_ver_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lake_instInhabitedInputVer_default(void){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_box(0);
return v___x_47_;
}
}
static lean_object* _init_l_Lake_instInhabitedInputVer(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
static lean_object* _init_l_Lake_instReprInputVer_repr___closed__2(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(2u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lake_instReprInputVer_repr___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(1u);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInputVer_repr(lean_object* v_x_68_, lean_object* v_prec_69_){
_start:
{
lean_object* v___y_71_; 
switch(lean_obj_tag(v_x_68_))
{
case 0:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1024u);
v___x_78_ = lean_nat_dec_le(v___x_77_, v_prec_69_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_71_ = v___x_79_;
goto v___jp_70_;
}
else
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_71_ = v___x_80_;
goto v___jp_70_;
}
}
case 1:
{
lean_object* v_rev_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_101_; 
v_rev_81_ = lean_ctor_get(v_x_68_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_68_);
if (v_isSharedCheck_101_ == 0)
{
v___x_83_ = v_x_68_;
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_rev_81_);
lean_dec(v_x_68_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_101_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___y_86_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_69_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_86_ = v___x_99_;
goto v___jp_85_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_86_ = v___x_100_;
goto v___jp_85_;
}
v___jp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_87_ = ((lean_object*)(l_Lake_instReprInputVer_repr___closed__6));
v___x_88_ = l_String_quote(v_rev_81_);
if (v_isShared_84_ == 0)
{
lean_ctor_set_tag(v___x_83_, 3);
lean_ctor_set(v___x_83_, 0, v___x_88_);
v___x_90_ = v___x_83_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_96_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_87_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
lean_inc(v___y_86_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___y_86_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_93_);
v___x_95_ = l_Repr_addAppParen(v___x_94_, v_prec_69_);
return v___x_95_;
}
}
}
}
default: 
{
lean_object* v_ver_102_; lean_object* v___y_104_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_ver_102_ = lean_ctor_get(v_x_68_, 0);
lean_inc_ref(v_ver_102_);
lean_dec_ref_known(v_x_68_, 1);
v___x_112_ = lean_unsigned_to_nat(1024u);
v___x_113_ = lean_nat_dec_le(v___x_112_, v_prec_69_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_104_ = v___x_114_;
goto v___jp_103_;
}
else
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_104_ = v___x_115_;
goto v___jp_103_;
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_105_ = ((lean_object*)(l_Lake_instReprInputVer_repr___closed__9));
v___x_106_ = l_Lake_instReprVerRange_repr___redArg(v_ver_102_);
v___x_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
lean_inc(v___y_104_);
v___x_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_108_, 0, v___y_104_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = 0;
v___x_110_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v___x_109_);
v___x_111_ = l_Repr_addAppParen(v___x_110_, v_prec_69_);
return v___x_111_;
}
}
}
v___jp_70_:
{
lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_72_ = ((lean_object*)(l_Lake_instReprInputVer_repr___closed__1));
lean_inc(v___y_71_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___y_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = 0;
v___x_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_74_);
v___x_76_ = l_Repr_addAppParen(v___x_75_, v_prec_69_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInputVer_repr___boxed(lean_object* v_x_116_, lean_object* v_prec_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lake_instReprInputVer_repr(v_x_116_, v_prec_117_);
lean_dec(v_prec_117_);
return v_res_118_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0));
v___x_123_ = lean_string_utf8_byte_size(v___x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(lean_object* v_s_124_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_125_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0));
v___x_126_ = lean_string_utf8_byte_size(v_s_124_);
v___x_127_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__1, &l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__1);
v___x_128_ = lean_nat_dec_le(v___x_127_, v___x_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec_ref(v_s_124_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_string_memcmp(v_s_124_, v___x_125_, v___x_130_, v___x_130_, v___x_127_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; 
lean_dec_ref(v_s_124_);
v___x_132_ = lean_box(0);
return v___x_132_;
}
else
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
lean_inc_ref(v_s_124_);
v___x_133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_133_, 0, v_s_124_);
lean_ctor_set(v___x_133_, 1, v___x_130_);
lean_ctor_set(v___x_133_, 2, v___x_126_);
v___x_134_ = l_String_Slice_pos_x21(v___x_133_, v___x_127_);
lean_dec_ref_known(v___x_133_, 3);
v___x_135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_135_, 0, v_s_124_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
lean_ctor_set(v___x_135_, 2, v___x_126_);
v___x_136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(lean_object* v_s_137_, lean_object* v_pat_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(v_s_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___boxed(lean_object* v_s_140_, lean_object* v_pat_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(v_s_140_, v_pat_141_);
lean_dec_ref(v_pat_141_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_parse(lean_object* v_ver_143_){
_start:
{
lean_object* v___x_144_; 
lean_inc_ref(v_ver_143_);
v___x_144_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(v_ver_143_);
if (lean_obj_tag(v___x_144_) == 1)
{
lean_object* v_val_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_154_; 
lean_dec_ref(v_ver_143_);
v_val_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_154_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_val_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_154_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = l_String_Slice_toString(v_val_145_);
lean_dec(v_val_145_);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_149_);
v___x_151_ = v_reuseFailAlloc_153_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
}
}
else
{
lean_object* v___x_155_; 
lean_dec(v___x_144_);
v___x_155_ = l_Lake_VerRange_parse(v_ver_143_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_155_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_155_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_172_; 
v_a_164_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_172_ == 0)
{
v___x_166_ = v___x_155_;
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_155_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_172_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_168_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_168_, 0, v_a_164_);
if (v_isShared_167_ == 0)
{
lean_ctor_set(v___x_166_, 0, v___x_168_);
v___x_170_ = v___x_166_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_toString_x3f(lean_object* v_self_175_){
_start:
{
switch(lean_obj_tag(v_self_175_))
{
case 0:
{
lean_object* v___x_176_; 
v___x_176_ = lean_box(0);
return v___x_176_;
}
case 1:
{
lean_object* v_rev_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_186_; 
v_rev_177_ = lean_ctor_get(v_self_175_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_self_175_);
if (v_isSharedCheck_186_ == 0)
{
v___x_179_ = v_self_175_;
v_isShared_180_ = v_isSharedCheck_186_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_rev_177_);
lean_dec(v_self_175_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_186_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; 
v___x_181_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0));
v___x_182_ = lean_string_append(v___x_181_, v_rev_177_);
lean_dec_ref(v_rev_177_);
if (v_isShared_180_ == 0)
{
lean_ctor_set(v___x_179_, 0, v___x_182_);
v___x_184_ = v___x_179_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
default: 
{
lean_object* v_ver_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_195_; 
v_ver_187_ = lean_ctor_get(v_self_175_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v_self_175_);
if (v_isSharedCheck_195_ == 0)
{
v___x_189_ = v_self_175_;
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_ver_187_);
lean_dec(v_self_175_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_195_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v_toString_191_; lean_object* v___x_193_; 
v_toString_191_ = lean_ctor_get(v_ver_187_, 0);
lean_inc_ref(v_toString_191_);
lean_dec_ref(v_ver_187_);
if (v_isShared_190_ == 0)
{
lean_ctor_set_tag(v___x_189_, 1);
lean_ctor_set(v___x_189_, 0, v_toString_191_);
v___x_193_ = v___x_189_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_toString_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx(lean_object* v_x_196_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
lean_object* v___x_197_; 
v___x_197_ = lean_unsigned_to_nat(0u);
return v___x_197_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = lean_unsigned_to_nat(1u);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___boxed(lean_object* v_x_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_DependencySrc_ctorIdx(v_x_199_);
lean_dec_ref(v_x_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___redArg(lean_object* v_t_201_, lean_object* v_k_202_){
_start:
{
if (lean_obj_tag(v_t_201_) == 0)
{
lean_object* v_dir_203_; lean_object* v___x_204_; 
v_dir_203_ = lean_ctor_get(v_t_201_, 0);
lean_inc_ref(v_dir_203_);
lean_dec_ref_known(v_t_201_, 1);
v___x_204_ = lean_apply_1(v_k_202_, v_dir_203_);
return v___x_204_;
}
else
{
lean_object* v_url_205_; lean_object* v_rev_206_; lean_object* v_subDir_207_; lean_object* v___x_208_; 
v_url_205_ = lean_ctor_get(v_t_201_, 0);
lean_inc_ref(v_url_205_);
v_rev_206_ = lean_ctor_get(v_t_201_, 1);
lean_inc(v_rev_206_);
v_subDir_207_ = lean_ctor_get(v_t_201_, 2);
lean_inc(v_subDir_207_);
lean_dec_ref_known(v_t_201_, 3);
v___x_208_ = lean_apply_3(v_k_202_, v_url_205_, v_rev_206_, v_subDir_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim(lean_object* v_motive_209_, lean_object* v_ctorIdx_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_k_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_211_, v_k_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___boxed(lean_object* v_motive_215_, lean_object* v_ctorIdx_216_, lean_object* v_t_217_, lean_object* v_h_218_, lean_object* v_k_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lake_DependencySrc_ctorElim(v_motive_215_, v_ctorIdx_216_, v_t_217_, v_h_218_, v_k_219_);
lean_dec(v_ctorIdx_216_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim___redArg(lean_object* v_t_221_, lean_object* v_path_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_221_, v_path_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_path_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_225_, v_path_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim___redArg(lean_object* v_t_229_, lean_object* v_git_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_229_, v_git_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim(lean_object* v_motive_232_, lean_object* v_t_233_, lean_object* v_h_234_, lean_object* v_git_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_233_, v_git_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_250_; 
v___x_250_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return v___x_250_;
}
else
{
lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_262_; 
v_val_251_ = lean_ctor_get(v_x_248_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_262_ == 0)
{
v___x_253_ = v_x_248_;
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_dec(v_x_248_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_262_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_255_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
v___x_256_ = l_String_quote(v_val_251_);
if (v_isShared_254_ == 0)
{
lean_ctor_set_tag(v___x_253_, 3);
lean_ctor_set(v___x_253_, 0, v___x_256_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_256_);
v___x_258_ = v_reuseFailAlloc_261_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_255_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = l_Repr_addAppParen(v___x_259_, v_x_249_);
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_x_263_, v_x_264_);
lean_dec(v_x_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
lean_object* v___x_271_; 
v___x_271_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return v___x_271_;
}
else
{
lean_object* v_val_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_287_; 
v_val_272_ = lean_ctor_get(v_x_269_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_269_);
if (v_isSharedCheck_287_ == 0)
{
v___x_274_ = v_x_269_;
v_isShared_275_ = v_isSharedCheck_287_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_val_272_);
lean_dec(v_x_269_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_287_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_281_; 
v___x_276_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
v___x_277_ = lean_unsigned_to_nat(1024u);
v___x_278_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
v___x_279_ = l_String_quote(v_val_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set_tag(v___x_274_, 3);
lean_ctor_set(v___x_274_, 0, v___x_279_);
v___x_281_ = v___x_274_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_286_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_278_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Repr_addAppParen(v___x_282_, v___x_277_);
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_276_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = l_Repr_addAppParen(v___x_284_, v_x_270_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(lean_object* v_x_288_, lean_object* v_x_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_x_288_, v_x_289_);
lean_dec(v_x_289_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr(lean_object* v_x_303_, lean_object* v_prec_304_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v_dir_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_329_; 
v_dir_305_ = lean_ctor_get(v_x_303_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_329_ == 0)
{
v___x_307_ = v_x_303_;
v_isShared_308_ = v_isSharedCheck_329_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_dir_305_);
lean_dec(v_x_303_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_329_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___y_310_; lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(1024u);
v___x_326_ = lean_nat_dec_le(v___x_325_, v_prec_304_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_310_ = v___x_327_;
goto v___jp_309_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_310_ = v___x_328_;
goto v___jp_309_;
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_311_ = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__2));
v___x_312_ = lean_unsigned_to_nat(1024u);
v___x_313_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
v___x_314_ = l_String_quote(v_dir_305_);
if (v_isShared_308_ == 0)
{
lean_ctor_set_tag(v___x_307_, 3);
lean_ctor_set(v___x_307_, 0, v___x_314_);
v___x_316_ = v___x_307_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_324_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_313_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = l_Repr_addAppParen(v___x_317_, v___x_312_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_311_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_inc(v___y_310_);
v___x_320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_310_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = 0;
v___x_322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_321_);
v___x_323_ = l_Repr_addAppParen(v___x_322_, v_prec_304_);
return v___x_323_;
}
}
}
}
else
{
lean_object* v_url_330_; lean_object* v_rev_331_; lean_object* v_subDir_332_; lean_object* v___y_334_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_url_330_ = lean_ctor_get(v_x_303_, 0);
lean_inc_ref(v_url_330_);
v_rev_331_ = lean_ctor_get(v_x_303_, 1);
lean_inc(v_rev_331_);
v_subDir_332_ = lean_ctor_get(v_x_303_, 2);
lean_inc(v_subDir_332_);
lean_dec_ref_known(v_x_303_, 3);
v___x_351_ = lean_unsigned_to_nat(1024u);
v___x_352_ = lean_nat_dec_le(v___x_351_, v_prec_304_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_334_ = v___x_353_;
goto v___jp_333_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_334_ = v___x_354_;
goto v___jp_333_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_335_ = lean_box(1);
v___x_336_ = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__5));
v___x_337_ = l_String_quote(v_url_330_);
v___x_338_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_336_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_335_);
v___x_341_ = lean_unsigned_to_nat(1024u);
v___x_342_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_rev_331_, v___x_341_);
v___x_343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_335_);
v___x_345_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_subDir_332_, v___x_341_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
lean_inc(v___y_334_);
v___x_347_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_347_, 0, v___y_334_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = 0;
v___x_349_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*1, v___x_348_);
v___x_350_ = l_Repr_addAppParen(v___x_349_, v_prec_304_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr___boxed(lean_object* v_x_355_, lean_object* v_prec_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lake_instReprDependencySrc_repr(v_x_355_, v_prec_356_);
lean_dec(v_prec_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_dirName(lean_object* v_dep_375_){
_start:
{
lean_object* v_name_376_; uint8_t v___x_377_; lean_object* v___x_378_; 
v_name_376_ = lean_ctor_get(v_dep_375_, 0);
lean_inc(v_name_376_);
lean_dec_ref(v_dep_375_);
v___x_377_ = 0;
v___x_378_ = l_Lean_Name_toString(v_name_376_, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_prettyName(lean_object* v_dep_379_){
_start:
{
lean_object* v_name_380_; uint8_t v___x_381_; lean_object* v___x_382_; 
v_name_380_ = lean_ctor_get(v_dep_379_, 0);
lean_inc(v_name_380_);
lean_dec_ref(v_dep_379_);
v___x_381_ = 0;
v___x_382_ = l_Lean_Name_toString(v_name_380_, v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_reservoirName(lean_object* v_dep_383_){
_start:
{
lean_object* v_name_384_; uint8_t v___x_385_; lean_object* v___x_386_; 
v_name_384_ = lean_ctor_get(v_dep_383_, 0);
lean_inc(v_name_384_);
lean_dec_ref(v_dep_383_);
v___x_385_ = 0;
v___x_386_ = l_Lean_Name_toString(v_name_384_, v___x_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object* v_dep_388_){
_start:
{
lean_object* v_name_389_; lean_object* v_scope_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_name_389_ = lean_ctor_get(v_dep_388_, 0);
lean_inc(v_name_389_);
v_scope_390_ = lean_ctor_get(v_dep_388_, 1);
lean_inc_ref(v_scope_390_);
lean_dec_ref(v_dep_388_);
v___x_391_ = ((lean_object*)(l_Lake_Dependency_fullName___closed__0));
v___x_392_ = lean_string_append(v_scope_390_, v___x_391_);
v___x_393_ = 0;
v___x_394_ = l_Lean_Name_toString(v_name_389_, v___x_393_);
v___x_395_ = lean_string_append(v___x_392_, v___x_394_);
lean_dec_ref(v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_resolverDescr(lean_object* v_dep_397_){
_start:
{
lean_object* v_name_398_; lean_object* v_scope_399_; lean_object* v_version_400_; lean_object* v___y_402_; uint8_t v___x_409_; lean_object* v_name_410_; lean_object* v___x_411_; 
v_name_398_ = lean_ctor_get(v_dep_397_, 0);
lean_inc(v_name_398_);
v_scope_399_ = lean_ctor_get(v_dep_397_, 1);
lean_inc_ref(v_scope_399_);
v_version_400_ = lean_ctor_get(v_dep_397_, 2);
lean_inc(v_version_400_);
lean_dec_ref(v_dep_397_);
v___x_409_ = 0;
v_name_410_ = l_Lean_Name_toString(v_name_398_, v___x_409_);
v___x_411_ = l_Lake_InputVer_toString_x3f(v_version_400_);
if (lean_obj_tag(v___x_411_) == 0)
{
v___y_402_ = v_name_410_;
goto v___jp_401_;
}
else
{
lean_object* v_val_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v_val_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_val_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = ((lean_object*)(l_Lake_Dependency_resolverDescr___closed__0));
v___x_414_ = lean_string_append(v_name_410_, v___x_413_);
v___x_415_ = lean_string_append(v___x_414_, v_val_412_);
lean_dec(v_val_412_);
v___y_402_ = v___x_415_;
goto v___jp_401_;
}
v___jp_401_:
{
lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_403_ = lean_string_utf8_byte_size(v_scope_399_);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_nat_dec_eq(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = ((lean_object*)(l_Lake_Dependency_fullName___closed__0));
v___x_407_ = lean_string_append(v_scope_399_, v___x_406_);
v___x_408_ = lean_string_append(v___x_407_, v___y_402_);
lean_dec_ref(v___y_402_);
return v___x_408_;
}
else
{
lean_dec_ref(v_scope_399_);
return v___y_402_;
}
}
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_FilePath(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Version(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedInputVer_default = _init_l_Lake_instInhabitedInputVer_default();
lean_mark_persistent(l_Lake_instInhabitedInputVer_default);
l_Lake_instInhabitedInputVer = _init_l_Lake_instInhabitedInputVer();
lean_mark_persistent(l_Lake_instInhabitedInputVer);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Dependency(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Init_System_FilePath(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Lean_Data_NameMap_Basic(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Dependency(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Dependency(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Dependency(builtin);
}
#ifdef __cplusplus
}
#endif

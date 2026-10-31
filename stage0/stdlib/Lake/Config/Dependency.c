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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lake_instReprVerRange_repr___redArg(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lake_VerRange_parse(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_parse(lean_object*);
static const lean_closure_object l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_InputVer_parse, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0 = (const lean_object*)&l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion = (const lean_object*)&l___private_Lake_Config_Dependency_0__Lake_InputVer_instDecodeVersion___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_InputVer_toString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instInhabitedDependencySrc_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedDependencySrc_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedDependencySrc_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedDependencySrc_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_string_object l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_ = (const lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value;
static const lean_string_object l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Dependency"};
static const lean_object* l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_ = (const lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value;
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instImpl___closed__0_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value_aux_0),((lean_object*)&l_Lake_instImpl___closed__1_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value),LEAN_SCALAR_PTR_LITERAL(248, 114, 43, 207, 103, 109, 40, 59)}};
static const lean_object* l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value;
LEAN_EXPORT const lean_object* l_Lake_instImpl_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24_ = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameDependency = (const lean_object*)&l_Lake_instImpl___closed__2_00___x40_Lake_Config_Dependency_35947708____hygCtx___hyg_24__value;
LEAN_EXPORT lean_object* l_Lake_Dependency_dirName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_prettyName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Dependency_reservoirName(lean_object*);
static const lean_string_object l_Lake_Dependency_fullName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_Dependency_fullName___closed__0 = (const lean_object*)&l_Lake_Dependency_fullName___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object*);
static const lean_string_object l_Lake_Dependency_resolverDescr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_Lake_Dependency_resolverDescr___closed__0 = (const lean_object*)&l_Lake_Dependency_resolverDescr___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Dependency_resolverDescr(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lake_InputVer_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_rev_7_; lean_object* v___x_8_; 
v_rev_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_rev_7_);
lean_dec(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_rev_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lake_InputVer_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_InputVer_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_none_elim___redArg(lean_object* v_t_21_, lean_object* v_none_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lake_InputVer_ctorElim___redArg(v_t_21_, v_none_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_none_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_none_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lake_InputVer_ctorElim___redArg(v_t_25_, v_none_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_git_elim___redArg(lean_object* v_t_29_, lean_object* v_git_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lake_InputVer_ctorElim___redArg(v_t_29_, v_git_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_git_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_git_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lake_InputVer_ctorElim___redArg(v_t_33_, v_git_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ver_elim___redArg(lean_object* v_t_37_, lean_object* v_ver_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lake_InputVer_ctorElim___redArg(v_t_37_, v_ver_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_ver_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_ver_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lake_InputVer_ctorElim___redArg(v_t_41_, v_ver_43_);
return v___x_44_;
}
}
static lean_object* _init_l_Lake_instInhabitedInputVer_default(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Lake_instInhabitedInputVer(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
static lean_object* _init_l_Lake_instReprInputVer_repr___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_unsigned_to_nat(2u);
v___x_51_ = lean_nat_to_int(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l_Lake_instReprInputVer_repr___closed__3(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_unsigned_to_nat(1u);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInputVer_repr(lean_object* v_x_66_, lean_object* v_prec_67_){
_start:
{
lean_object* v___y_69_; 
switch(lean_obj_tag(v_x_66_))
{
case 0:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(1024u);
v___x_76_ = lean_nat_dec_le(v___x_75_, v_prec_67_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_69_ = v___x_77_;
goto v___jp_68_;
}
else
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_69_ = v___x_78_;
goto v___jp_68_;
}
}
case 1:
{
lean_object* v_rev_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_99_; 
v_rev_79_ = lean_ctor_get(v_x_66_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_66_);
if (v_isSharedCheck_99_ == 0)
{
v___x_81_ = v_x_66_;
v_isShared_82_ = v_isSharedCheck_99_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_rev_79_);
lean_dec(v_x_66_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_99_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___y_84_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_95_ = lean_unsigned_to_nat(1024u);
v___x_96_ = lean_nat_dec_le(v___x_95_, v_prec_67_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_84_ = v___x_97_;
goto v___jp_83_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_84_ = v___x_98_;
goto v___jp_83_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_85_ = ((lean_object*)(l_Lake_instReprInputVer_repr___closed__6));
v___x_86_ = l_String_quote(v_rev_79_);
if (v_isShared_82_ == 0)
{
lean_ctor_set_tag(v___x_81_, 3);
lean_ctor_set(v___x_81_, 0, v___x_86_);
v___x_88_ = v___x_81_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_94_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_85_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
lean_inc(v___y_84_);
v___x_90_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_90_, 0, v___y_84_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = 0;
v___x_92_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*1, v___x_91_);
v___x_93_ = l_Repr_addAppParen(v___x_92_, v_prec_67_);
return v___x_93_;
}
}
}
}
default: 
{
lean_object* v_ver_100_; lean_object* v___y_102_; lean_object* v___x_110_; uint8_t v___x_111_; 
v_ver_100_ = lean_ctor_get(v_x_66_, 0);
lean_inc_ref(v_ver_100_);
lean_dec_ref_known(v_x_66_, 1);
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_67_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_102_ = v___x_112_;
goto v___jp_101_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_102_ = v___x_113_;
goto v___jp_101_;
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_103_ = ((lean_object*)(l_Lake_instReprInputVer_repr___closed__9));
v___x_104_ = l_Lake_instReprVerRange_repr___redArg(v_ver_100_);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
lean_inc(v___y_102_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___y_102_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
v___x_109_ = l_Repr_addAppParen(v___x_108_, v_prec_67_);
return v___x_109_;
}
}
}
v___jp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_70_ = ((lean_object*)(l_Lake_instReprInputVer_repr___closed__1));
lean_inc(v___y_69_);
v___x_71_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_71_, 0, v___y_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = 0;
v___x_73_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set_uint8(v___x_73_, sizeof(void*)*1, v___x_72_);
v___x_74_ = l_Repr_addAppParen(v___x_73_, v_prec_67_);
return v___x_74_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInputVer_repr___boxed(lean_object* v_x_114_, lean_object* v_prec_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lake_instReprInputVer_repr(v_x_114_, v_prec_115_);
lean_dec(v_prec_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(lean_object* v_s_120_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_121_ = lean_string_utf8_byte_size(v_s_120_);
v___x_122_ = lean_unsigned_to_nat(4u);
v___x_123_ = lean_nat_dec_le(v___x_122_, v___x_121_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref(v_s_120_);
v___x_124_ = lean_box(0);
return v___x_124_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0));
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_string_memcmp(v_s_120_, v___x_125_, v___x_126_, v___x_126_, v___x_122_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_dec_ref(v_s_120_);
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_inc_ref(v_s_120_);
v___x_129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_129_, 0, v_s_120_);
lean_ctor_set(v___x_129_, 1, v___x_126_);
lean_ctor_set(v___x_129_, 2, v___x_121_);
v___x_130_ = l_String_Slice_pos_x21(v___x_129_, v___x_122_);
lean_dec_ref_known(v___x_129_, 3);
v___x_131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_131_, 0, v_s_120_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
lean_ctor_set(v___x_131_, 2, v___x_121_);
v___x_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(lean_object* v_s_133_, lean_object* v_pat_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(v_s_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___boxed(lean_object* v_s_136_, lean_object* v_pat_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(v_s_136_, v_pat_137_);
lean_dec_ref(v_pat_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_parse(lean_object* v_ver_139_){
_start:
{
lean_object* v___x_140_; 
lean_inc_ref(v_ver_139_);
v___x_140_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(v_ver_139_);
if (lean_obj_tag(v___x_140_) == 1)
{
lean_object* v_val_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_150_; 
lean_dec_ref(v_ver_139_);
v_val_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_150_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_val_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_150_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_145_ = l_String_Slice_toString(v_val_141_);
lean_dec(v_val_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_145_);
v___x_147_ = v___x_143_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_149_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
lean_object* v___x_148_; 
v___x_148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
return v___x_148_;
}
}
}
else
{
lean_object* v___x_151_; 
lean_dec(v___x_140_);
v___x_151_ = l_Lake_VerRange_parse(v_ver_139_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_151_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_151_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
else
{
lean_object* v_a_160_; lean_object* v___x_162_; uint8_t v_isShared_163_; uint8_t v_isSharedCheck_168_; 
v_a_160_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_168_ == 0)
{
v___x_162_ = v___x_151_;
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
else
{
lean_inc(v_a_160_);
lean_dec(v___x_151_);
v___x_162_ = lean_box(0);
v_isShared_163_ = v_isSharedCheck_168_;
goto v_resetjp_161_;
}
v_resetjp_161_:
{
lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_164_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_164_, 0, v_a_160_);
if (v_isShared_163_ == 0)
{
lean_ctor_set(v___x_162_, 0, v___x_164_);
v___x_166_ = v___x_162_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_toString_x3f(lean_object* v_self_171_){
_start:
{
switch(lean_obj_tag(v_self_171_))
{
case 0:
{
lean_object* v___x_172_; 
v___x_172_ = lean_box(0);
return v___x_172_;
}
case 1:
{
lean_object* v_rev_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_182_; 
v_rev_173_ = lean_ctor_get(v_self_171_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v_self_171_);
if (v_isSharedCheck_182_ == 0)
{
v___x_175_ = v_self_171_;
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_rev_173_);
lean_dec(v_self_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_177_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0));
v___x_178_ = lean_string_append(v___x_177_, v_rev_173_);
lean_dec_ref(v_rev_173_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
default: 
{
lean_object* v_ver_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_ver_183_ = lean_ctor_get(v_self_171_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v_self_171_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v_self_171_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_ver_183_);
lean_dec(v_self_171_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v_toString_187_; lean_object* v___x_189_; 
v_toString_187_ = lean_ctor_get(v_ver_183_, 0);
lean_inc_ref(v_toString_187_);
lean_dec_ref(v_ver_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 1);
lean_ctor_set(v___x_185_, 0, v_toString_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_toString_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___impl(lean_object* v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_tag_nat(v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___impl___boxed(lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lake_DependencySrc_ctorIdx___impl(v_x_194_);
lean_dec_ref(v_x_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___redArg(lean_object* v_t_196_, lean_object* v_k_197_){
_start:
{
if (lean_obj_tag(v_t_196_) == 0)
{
lean_object* v_dir_198_; uint8_t v_copy_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_dir_198_ = lean_ctor_get(v_t_196_, 0);
lean_inc_ref(v_dir_198_);
v_copy_199_ = lean_ctor_get_uint8(v_t_196_, sizeof(void*)*1);
lean_dec_ref_known(v_t_196_, 1);
v___x_200_ = lean_box(v_copy_199_);
v___x_201_ = lean_apply_2(v_k_197_, v_dir_198_, v___x_200_);
return v___x_201_;
}
else
{
lean_object* v_url_202_; lean_object* v_rev_203_; lean_object* v_subDir_204_; lean_object* v___x_205_; 
v_url_202_ = lean_ctor_get(v_t_196_, 0);
lean_inc_ref(v_url_202_);
v_rev_203_ = lean_ctor_get(v_t_196_, 1);
lean_inc(v_rev_203_);
v_subDir_204_ = lean_ctor_get(v_t_196_, 2);
lean_inc(v_subDir_204_);
lean_dec_ref_known(v_t_196_, 3);
v___x_205_ = lean_apply_3(v_k_197_, v_url_202_, v_rev_203_, v_subDir_204_);
return v___x_205_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim(lean_object* v_motive_206_, lean_object* v_ctorIdx_207_, lean_object* v_t_208_, lean_object* v_h_209_, lean_object* v_k_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_208_, v_k_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___boxed(lean_object* v_motive_212_, lean_object* v_ctorIdx_213_, lean_object* v_t_214_, lean_object* v_h_215_, lean_object* v_k_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_DependencySrc_ctorElim(v_motive_212_, v_ctorIdx_213_, v_t_214_, v_h_215_, v_k_216_);
lean_dec(v_ctorIdx_213_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim___redArg(lean_object* v_t_218_, lean_object* v_path_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_218_, v_path_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_path_elim(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_path_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_222_, v_path_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim___redArg(lean_object* v_t_226_, lean_object* v_git_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_226_, v_git_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_git_elim(lean_object* v_motive_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_git_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lake_DependencySrc_ctorElim___redArg(v_t_230_, v_git_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_246_) == 0)
{
lean_object* v___x_248_; 
v___x_248_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return v___x_248_;
}
else
{
lean_object* v_val_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_260_; 
v_val_249_ = lean_ctor_get(v_x_246_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_246_);
if (v_isSharedCheck_260_ == 0)
{
v___x_251_ = v_x_246_;
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_val_249_);
lean_dec(v_x_246_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_253_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
v___x_254_ = l_String_quote(v_val_249_);
if (v_isShared_252_ == 0)
{
lean_ctor_set_tag(v___x_251_, 3);
lean_ctor_set(v___x_251_, 0, v___x_254_);
v___x_256_ = v___x_251_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_259_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_253_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Repr_addAppParen(v___x_257_, v_x_247_);
return v___x_258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_x_261_, v_x_262_);
lean_dec(v_x_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
if (lean_obj_tag(v_x_267_) == 0)
{
lean_object* v___x_269_; 
v___x_269_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return v___x_269_;
}
else
{
lean_object* v_val_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_285_; 
v_val_270_ = lean_ctor_get(v_x_267_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v_x_267_);
if (v_isSharedCheck_285_ == 0)
{
v___x_272_ = v_x_267_;
v_isShared_273_ = v_isSharedCheck_285_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_val_270_);
lean_dec(v_x_267_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_285_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_274_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
v___x_275_ = lean_unsigned_to_nat(1024u);
v___x_276_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
v___x_277_ = l_String_quote(v_val_270_);
if (v_isShared_273_ == 0)
{
lean_ctor_set_tag(v___x_272_, 3);
lean_ctor_set(v___x_272_, 0, v___x_277_);
v___x_279_ = v___x_272_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_284_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_276_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Repr_addAppParen(v___x_280_, v___x_275_);
v___x_282_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_274_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = l_Repr_addAppParen(v___x_282_, v_x_268_);
return v___x_283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_x_286_, v_x_287_);
lean_dec(v_x_287_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr(lean_object* v_x_301_, lean_object* v_prec_302_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_dir_303_; uint8_t v_copy_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_332_; 
v_dir_303_ = lean_ctor_get(v_x_301_, 0);
v_copy_304_ = lean_ctor_get_uint8(v_x_301_, sizeof(void*)*1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_332_ == 0)
{
v___x_306_ = v_x_301_;
v_isShared_307_ = v_isSharedCheck_332_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_dir_303_);
lean_dec(v_x_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_332_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___y_309_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(1024u);
v___x_329_ = lean_nat_dec_le(v___x_328_, v_prec_302_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_309_ = v___x_330_;
goto v___jp_308_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_309_ = v___x_331_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_325_; 
v___x_310_ = lean_box(1);
v___x_311_ = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__2));
v___x_312_ = lean_unsigned_to_nat(1024u);
v___x_313_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
v___x_314_ = l_String_quote(v_dir_303_);
v___x_315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_313_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = l_Repr_addAppParen(v___x_316_, v___x_312_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_311_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_310_);
v___x_320_ = l_Bool_repr___redArg(v_copy_304_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_inc(v___y_309_);
v___x_322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_309_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = 0;
if (v_isShared_307_ == 0)
{
lean_ctor_set_tag(v___x_306_, 6);
lean_ctor_set(v___x_306_, 0, v___x_322_);
v___x_325_ = v___x_306_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_322_);
v___x_325_ = v_reuseFailAlloc_327_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; 
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*1, v___x_323_);
v___x_326_ = l_Repr_addAppParen(v___x_325_, v_prec_302_);
return v___x_326_;
}
}
}
}
else
{
lean_object* v_url_333_; lean_object* v_rev_334_; lean_object* v_subDir_335_; lean_object* v___y_337_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_url_333_ = lean_ctor_get(v_x_301_, 0);
lean_inc_ref(v_url_333_);
v_rev_334_ = lean_ctor_get(v_x_301_, 1);
lean_inc(v_rev_334_);
v_subDir_335_ = lean_ctor_get(v_x_301_, 2);
lean_inc(v_subDir_335_);
lean_dec_ref_known(v_x_301_, 3);
v___x_354_ = lean_unsigned_to_nat(1024u);
v___x_355_ = lean_nat_dec_le(v___x_354_, v_prec_302_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_337_ = v___x_356_;
goto v___jp_336_;
}
else
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_337_ = v___x_357_;
goto v___jp_336_;
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_338_ = lean_box(1);
v___x_339_ = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__5));
v___x_340_ = l_String_quote(v_url_333_);
v___x_341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_339_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_338_);
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_rev_334_, v___x_344_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_343_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_338_);
v___x_348_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_subDir_335_, v___x_344_);
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_347_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_inc(v___y_337_);
v___x_350_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_350_, 0, v___y_337_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = 0;
v___x_352_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*1, v___x_351_);
v___x_353_ = l_Repr_addAppParen(v___x_352_, v_prec_302_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr___boxed(lean_object* v_x_358_, lean_object* v_prec_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lake_instReprDependencySrc_repr(v_x_358_, v_prec_359_);
lean_dec(v_prec_359_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_dirName(lean_object* v_dep_378_){
_start:
{
lean_object* v_name_379_; uint8_t v___x_380_; lean_object* v___x_381_; 
v_name_379_ = lean_ctor_get(v_dep_378_, 0);
lean_inc(v_name_379_);
lean_dec_ref(v_dep_378_);
v___x_380_ = 0;
v___x_381_ = l_Lean_Name_toString(v_name_379_, v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_prettyName(lean_object* v_dep_382_){
_start:
{
lean_object* v_name_383_; uint8_t v___x_384_; lean_object* v___x_385_; 
v_name_383_ = lean_ctor_get(v_dep_382_, 0);
lean_inc(v_name_383_);
lean_dec_ref(v_dep_382_);
v___x_384_ = 0;
v___x_385_ = l_Lean_Name_toString(v_name_383_, v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_reservoirName(lean_object* v_dep_386_){
_start:
{
lean_object* v_name_387_; uint8_t v___x_388_; lean_object* v___x_389_; 
v_name_387_ = lean_ctor_get(v_dep_386_, 0);
lean_inc(v_name_387_);
lean_dec_ref(v_dep_386_);
v___x_388_ = 0;
v___x_389_ = l_Lean_Name_toString(v_name_387_, v___x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object* v_dep_391_){
_start:
{
lean_object* v_name_392_; lean_object* v_scope_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v_name_392_ = lean_ctor_get(v_dep_391_, 0);
lean_inc(v_name_392_);
v_scope_393_ = lean_ctor_get(v_dep_391_, 1);
lean_inc_ref(v_scope_393_);
lean_dec_ref(v_dep_391_);
v___x_394_ = ((lean_object*)(l_Lake_Dependency_fullName___closed__0));
v___x_395_ = lean_string_append(v_scope_393_, v___x_394_);
v___x_396_ = 0;
v___x_397_ = l_Lean_Name_toString(v_name_392_, v___x_396_);
v___x_398_ = lean_string_append(v___x_395_, v___x_397_);
lean_dec_ref(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_resolverDescr(lean_object* v_dep_400_){
_start:
{
lean_object* v_name_401_; lean_object* v_scope_402_; lean_object* v_version_403_; lean_object* v___y_405_; uint8_t v___x_412_; lean_object* v_name_413_; lean_object* v___x_414_; 
v_name_401_ = lean_ctor_get(v_dep_400_, 0);
lean_inc(v_name_401_);
v_scope_402_ = lean_ctor_get(v_dep_400_, 1);
lean_inc_ref(v_scope_402_);
v_version_403_ = lean_ctor_get(v_dep_400_, 2);
lean_inc(v_version_403_);
lean_dec_ref(v_dep_400_);
v___x_412_ = 0;
v_name_413_ = l_Lean_Name_toString(v_name_401_, v___x_412_);
v___x_414_ = l_Lake_InputVer_toString_x3f(v_version_403_);
if (lean_obj_tag(v___x_414_) == 0)
{
v___y_405_ = v_name_413_;
goto v___jp_404_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_val_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = ((lean_object*)(l_Lake_Dependency_resolverDescr___closed__0));
v___x_417_ = lean_string_append(v_name_413_, v___x_416_);
v___x_418_ = lean_string_append(v___x_417_, v_val_415_);
lean_dec(v_val_415_);
v___y_405_ = v___x_418_;
goto v___jp_404_;
}
v___jp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_406_ = lean_string_utf8_byte_size(v_scope_402_);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_nat_dec_eq(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = ((lean_object*)(l_Lake_Dependency_fullName___closed__0));
v___x_410_ = lean_string_append(v_scope_402_, v___x_409_);
v___x_411_ = lean_string_append(v___x_410_, v___y_405_);
lean_dec_ref(v___y_405_);
return v___x_411_;
}
else
{
lean_dec_ref(v_scope_402_);
return v___y_405_;
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
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Dependency(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
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

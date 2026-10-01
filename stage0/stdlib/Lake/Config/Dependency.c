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
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(lean_object* v_s_122_){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_123_ = lean_string_utf8_byte_size(v_s_122_);
v___x_124_ = lean_unsigned_to_nat(4u);
v___x_125_ = lean_nat_dec_le(v___x_124_, v___x_123_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_dec_ref(v_s_122_);
v___x_126_ = lean_box(0);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0));
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_string_memcmp(v_s_122_, v___x_127_, v___x_128_, v___x_128_, v___x_124_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v_s_122_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_inc_ref(v_s_122_);
v___x_131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_131_, 0, v_s_122_);
lean_ctor_set(v___x_131_, 1, v___x_128_);
lean_ctor_set(v___x_131_, 2, v___x_123_);
v___x_132_ = l_String_Slice_pos_x21(v___x_131_, v___x_124_);
lean_dec_ref_known(v___x_131_, 3);
v___x_133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_133_, 0, v_s_122_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
lean_ctor_set(v___x_133_, 2, v___x_123_);
v___x_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(lean_object* v_s_135_, lean_object* v_pat_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(v_s_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___boxed(lean_object* v_s_138_, lean_object* v_pat_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0(v_s_138_, v_pat_139_);
lean_dec_ref(v_pat_139_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_parse(lean_object* v_ver_141_){
_start:
{
lean_object* v___x_142_; 
lean_inc_ref(v_ver_141_);
v___x_142_ = l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg(v_ver_141_);
if (lean_obj_tag(v___x_142_) == 1)
{
lean_object* v_val_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_152_; 
lean_dec_ref(v_ver_141_);
v_val_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_152_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_val_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_152_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = l_String_Slice_toString(v_val_143_);
lean_dec(v_val_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_147_);
v___x_149_ = v_reuseFailAlloc_151_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
}
}
else
{
lean_object* v___x_153_; 
lean_dec(v___x_142_);
v___x_153_ = l_Lake_VerRange_parse(v_ver_141_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_170_; 
v_a_162_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_170_ == 0)
{
v___x_164_ = v___x_153_;
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_153_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_170_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_166_, 0, v_a_162_);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 0, v___x_166_);
v___x_168_ = v___x_164_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InputVer_toString_x3f(lean_object* v_self_173_){
_start:
{
switch(lean_obj_tag(v_self_173_))
{
case 0:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
case 1:
{
lean_object* v_rev_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_184_; 
v_rev_175_ = lean_ctor_get(v_self_173_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v_self_173_);
if (v_isSharedCheck_184_ == 0)
{
v___x_177_ = v_self_173_;
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_rev_175_);
lean_dec(v_self_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_179_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00Lake_InputVer_parse_spec__0___redArg___closed__0));
v___x_180_ = lean_string_append(v___x_179_, v_rev_175_);
lean_dec_ref(v_rev_175_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_180_);
v___x_182_ = v___x_177_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
default: 
{
lean_object* v_ver_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_ver_185_ = lean_ctor_get(v_self_173_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_self_173_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v_self_173_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_ver_185_);
lean_dec(v_self_173_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_toString_189_; lean_object* v___x_191_; 
v_toString_189_ = lean_ctor_get(v_ver_185_, 0);
lean_inc_ref(v_toString_189_);
lean_dec_ref(v_ver_185_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 1);
lean_ctor_set(v___x_187_, 0, v_toString_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_toString_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx(lean_object* v_x_194_){
_start:
{
if (lean_obj_tag(v_x_194_) == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_unsigned_to_nat(0u);
return v___x_195_;
}
else
{
lean_object* v___x_196_; 
v___x_196_ = lean_unsigned_to_nat(1u);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorIdx___boxed(lean_object* v_x_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lake_DependencySrc_ctorIdx(v_x_197_);
lean_dec_ref(v_x_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_ctorElim___redArg(lean_object* v_t_199_, lean_object* v_k_200_){
_start:
{
if (lean_obj_tag(v_t_199_) == 0)
{
lean_object* v_dir_201_; uint8_t v_copy_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_dir_201_ = lean_ctor_get(v_t_199_, 0);
lean_inc_ref(v_dir_201_);
v_copy_202_ = lean_ctor_get_uint8(v_t_199_, sizeof(void*)*1);
lean_dec_ref_known(v_t_199_, 1);
v___x_203_ = lean_box(v_copy_202_);
v___x_204_ = lean_apply_2(v_k_200_, v_dir_201_, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_url_205_; lean_object* v_rev_206_; lean_object* v_subDir_207_; lean_object* v___x_208_; 
v_url_205_ = lean_ctor_get(v_t_199_, 0);
lean_inc_ref(v_url_205_);
v_rev_206_ = lean_ctor_get(v_t_199_, 1);
lean_inc(v_rev_206_);
v_subDir_207_ = lean_ctor_get(v_t_199_, 2);
lean_inc(v_subDir_207_);
lean_dec_ref_known(v_t_199_, 3);
v___x_208_ = lean_apply_3(v_k_200_, v_url_205_, v_rev_206_, v_subDir_207_);
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
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_249_) == 0)
{
lean_object* v___x_251_; 
v___x_251_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return v___x_251_;
}
else
{
lean_object* v_val_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_263_; 
v_val_252_ = lean_ctor_get(v_x_249_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_263_ == 0)
{
v___x_254_ = v_x_249_;
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_val_252_);
lean_dec(v_x_249_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_256_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
v___x_257_ = l_String_quote(v_val_252_);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 3);
lean_ctor_set(v___x_254_, 0, v___x_257_);
v___x_259_ = v___x_254_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_262_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_256_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = l_Repr_addAppParen(v___x_260_, v_x_250_);
return v___x_261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___boxed(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_x_264_, v_x_265_);
lean_dec(v_x_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_object* v___x_272_; 
v___x_272_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__1));
return v___x_272_;
}
else
{
lean_object* v_val_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_288_; 
v_val_273_ = lean_ctor_get(v_x_270_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_270_);
if (v_isSharedCheck_288_ == 0)
{
v___x_275_ = v_x_270_;
v_isShared_276_ = v_isSharedCheck_288_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_val_273_);
lean_dec(v_x_270_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_288_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_277_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0___closed__3));
v___x_278_ = lean_unsigned_to_nat(1024u);
v___x_279_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
v___x_280_ = l_String_quote(v_val_273_);
if (v_isShared_276_ == 0)
{
lean_ctor_set_tag(v___x_275_, 3);
lean_ctor_set(v___x_275_, 0, v___x_280_);
v___x_282_ = v___x_275_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_287_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_279_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = l_Repr_addAppParen(v___x_283_, v___x_278_);
v___x_285_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_277_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = l_Repr_addAppParen(v___x_285_, v_x_271_);
return v___x_286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___boxed(lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_x_289_, v_x_290_);
lean_dec(v_x_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr(lean_object* v_x_304_, lean_object* v_prec_305_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v_dir_306_; uint8_t v_copy_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_335_; 
v_dir_306_ = lean_ctor_get(v_x_304_, 0);
v_copy_307_ = lean_ctor_get_uint8(v_x_304_, sizeof(void*)*1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_335_ == 0)
{
v___x_309_ = v_x_304_;
v_isShared_310_ = v_isSharedCheck_335_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_dir_306_);
lean_dec(v_x_304_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_335_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___y_312_; lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(1024u);
v___x_332_ = lean_nat_dec_le(v___x_331_, v_prec_305_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_312_ = v___x_333_;
goto v___jp_311_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_312_ = v___x_334_;
goto v___jp_311_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_328_; 
v___x_313_ = lean_box(1);
v___x_314_ = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__2));
v___x_315_ = lean_unsigned_to_nat(1024u);
v___x_316_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1___closed__1));
v___x_317_ = l_String_quote(v_dir_306_);
v___x_318_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_316_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = l_Repr_addAppParen(v___x_319_, v___x_315_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_314_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_313_);
v___x_323_ = l_Bool_repr___redArg(v_copy_307_);
v___x_324_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_inc(v___y_312_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_312_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = 0;
if (v_isShared_310_ == 0)
{
lean_ctor_set_tag(v___x_309_, 6);
lean_ctor_set(v___x_309_, 0, v___x_325_);
v___x_328_ = v___x_309_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_325_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
lean_ctor_set_uint8(v___x_328_, sizeof(void*)*1, v___x_326_);
v___x_329_ = l_Repr_addAppParen(v___x_328_, v_prec_305_);
return v___x_329_;
}
}
}
}
else
{
lean_object* v_url_336_; lean_object* v_rev_337_; lean_object* v_subDir_338_; lean_object* v___y_340_; lean_object* v___x_357_; uint8_t v___x_358_; 
v_url_336_ = lean_ctor_get(v_x_304_, 0);
lean_inc_ref(v_url_336_);
v_rev_337_ = lean_ctor_get(v_x_304_, 1);
lean_inc(v_rev_337_);
v_subDir_338_ = lean_ctor_get(v_x_304_, 2);
lean_inc(v_subDir_338_);
lean_dec_ref_known(v_x_304_, 3);
v___x_357_ = lean_unsigned_to_nat(1024u);
v___x_358_ = lean_nat_dec_le(v___x_357_, v_prec_305_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__2, &l_Lake_instReprInputVer_repr___closed__2_once, _init_l_Lake_instReprInputVer_repr___closed__2);
v___y_340_ = v___x_359_;
goto v___jp_339_;
}
else
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l_Lake_instReprInputVer_repr___closed__3, &l_Lake_instReprInputVer_repr___closed__3_once, _init_l_Lake_instReprInputVer_repr___closed__3);
v___y_340_ = v___x_360_;
goto v___jp_339_;
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_341_ = lean_box(1);
v___x_342_ = ((lean_object*)(l_Lake_instReprDependencySrc_repr___closed__5));
v___x_343_ = l_String_quote(v_url_336_);
v___x_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_342_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_341_);
v___x_347_ = lean_unsigned_to_nat(1024u);
v___x_348_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__0(v_rev_337_, v___x_347_);
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_346_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_341_);
v___x_351_ = l_Option_repr___at___00Lake_instReprDependencySrc_repr_spec__1(v_subDir_338_, v___x_347_);
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
lean_inc(v___y_340_);
v___x_353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_353_, 0, v___y_340_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = 0;
v___x_355_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_354_);
v___x_356_ = l_Repr_addAppParen(v___x_355_, v_prec_305_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprDependencySrc_repr___boxed(lean_object* v_x_361_, lean_object* v_prec_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lake_instReprDependencySrc_repr(v_x_361_, v_prec_362_);
lean_dec(v_prec_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_dirName(lean_object* v_dep_381_){
_start:
{
lean_object* v_name_382_; uint8_t v___x_383_; lean_object* v___x_384_; 
v_name_382_ = lean_ctor_get(v_dep_381_, 0);
lean_inc(v_name_382_);
lean_dec_ref(v_dep_381_);
v___x_383_ = 0;
v___x_384_ = l_Lean_Name_toString(v_name_382_, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_prettyName(lean_object* v_dep_385_){
_start:
{
lean_object* v_name_386_; uint8_t v___x_387_; lean_object* v___x_388_; 
v_name_386_ = lean_ctor_get(v_dep_385_, 0);
lean_inc(v_name_386_);
lean_dec_ref(v_dep_385_);
v___x_387_ = 0;
v___x_388_ = l_Lean_Name_toString(v_name_386_, v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_reservoirName(lean_object* v_dep_389_){
_start:
{
lean_object* v_name_390_; uint8_t v___x_391_; lean_object* v___x_392_; 
v_name_390_ = lean_ctor_get(v_dep_389_, 0);
lean_inc(v_name_390_);
lean_dec_ref(v_dep_389_);
v___x_391_ = 0;
v___x_392_ = l_Lean_Name_toString(v_name_390_, v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_fullName(lean_object* v_dep_394_){
_start:
{
lean_object* v_name_395_; lean_object* v_scope_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_name_395_ = lean_ctor_get(v_dep_394_, 0);
lean_inc(v_name_395_);
v_scope_396_ = lean_ctor_get(v_dep_394_, 1);
lean_inc_ref(v_scope_396_);
lean_dec_ref(v_dep_394_);
v___x_397_ = ((lean_object*)(l_Lake_Dependency_fullName___closed__0));
v___x_398_ = lean_string_append(v_scope_396_, v___x_397_);
v___x_399_ = 0;
v___x_400_ = l_Lean_Name_toString(v_name_395_, v___x_399_);
v___x_401_ = lean_string_append(v___x_398_, v___x_400_);
lean_dec_ref(v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_resolverDescr(lean_object* v_dep_403_){
_start:
{
lean_object* v_name_404_; lean_object* v_scope_405_; lean_object* v_version_406_; lean_object* v___y_408_; uint8_t v___x_415_; lean_object* v_name_416_; lean_object* v___x_417_; 
v_name_404_ = lean_ctor_get(v_dep_403_, 0);
lean_inc(v_name_404_);
v_scope_405_ = lean_ctor_get(v_dep_403_, 1);
lean_inc_ref(v_scope_405_);
v_version_406_ = lean_ctor_get(v_dep_403_, 2);
lean_inc(v_version_406_);
lean_dec_ref(v_dep_403_);
v___x_415_ = 0;
v_name_416_ = l_Lean_Name_toString(v_name_404_, v___x_415_);
v___x_417_ = l_Lake_InputVer_toString_x3f(v_version_406_);
if (lean_obj_tag(v___x_417_) == 0)
{
v___y_408_ = v_name_416_;
goto v___jp_407_;
}
else
{
lean_object* v_val_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_val_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v___x_417_, 1);
v___x_419_ = ((lean_object*)(l_Lake_Dependency_resolverDescr___closed__0));
v___x_420_ = lean_string_append(v_name_416_, v___x_419_);
v___x_421_ = lean_string_append(v___x_420_, v_val_418_);
lean_dec(v_val_418_);
v___y_408_ = v___x_421_;
goto v___jp_407_;
}
v___jp_407_:
{
lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_409_ = lean_string_utf8_byte_size(v_scope_405_);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_nat_dec_eq(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = ((lean_object*)(l_Lake_Dependency_fullName___closed__0));
v___x_413_ = lean_string_append(v_scope_405_, v___x_412_);
v___x_414_ = lean_string_append(v___x_413_, v___y_408_);
lean_dec_ref(v___y_408_);
return v___x_414_;
}
else
{
lean_dec_ref(v_scope_405_);
return v___y_408_;
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

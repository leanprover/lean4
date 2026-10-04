// Lean compiler output
// Module: Lake.Config.LeanConfig
// Imports: public import Lake.Build.Target.Basic public import Lake.Config.Dynlib public import Lake.Config.MetaClasses public import Init.Data.String.Modify meta import all Lake.Config.Meta import Lake.Util.Name import Init.Data.String.Modify import Lake.Config.Meta
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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_Target_repr___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_instReprLeanOption_repr___redArg(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_instReprBackend_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lake.Backend.c"};
static const lean_object* l_Lake_instReprBackend_repr___closed__0 = (const lean_object*)&l_Lake_instReprBackend_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprBackend_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBackend_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprBackend_repr___closed__1 = (const lean_object*)&l_Lake_instReprBackend_repr___closed__1_value;
static const lean_string_object l_Lake_instReprBackend_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lake.Backend.llvm"};
static const lean_object* l_Lake_instReprBackend_repr___closed__2 = (const lean_object*)&l_Lake_instReprBackend_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprBackend_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBackend_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprBackend_repr___closed__3 = (const lean_object*)&l_Lake_instReprBackend_repr___closed__3_value;
static const lean_string_object l_Lake_instReprBackend_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.Backend.default"};
static const lean_object* l_Lake_instReprBackend_repr___closed__4 = (const lean_object*)&l_Lake_instReprBackend_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprBackend_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBackend_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprBackend_repr___closed__5 = (const lean_object*)&l_Lake_instReprBackend_repr___closed__5_value;
static lean_once_cell_t l_Lake_instReprBackend_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBackend_repr___closed__6;
static lean_once_cell_t l_Lake_instReprBackend_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprBackend_repr___closed__7;
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprBackend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprBackend_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprBackend___closed__0 = (const lean_object*)&l_Lake_instReprBackend___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprBackend = (const lean_object*)&l_Lake_instReprBackend___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Backend_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBackend(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBackend___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Backend_instInhabited;
static const lean_string_object l_Lake_Backend_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lake_Backend_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_Backend_ofString_x3f___closed__0_value;
static const lean_string_object l_Lake_Backend_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "llvm"};
static const lean_object* l_Lake_Backend_ofString_x3f___closed__1 = (const lean_object*)&l_Lake_Backend_ofString_x3f___closed__1_value;
static const lean_string_object l_Lake_Backend_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "default"};
static const lean_object* l_Lake_Backend_ofString_x3f___closed__2 = (const lean_object*)&l_Lake_Backend_ofString_x3f___closed__2_value;
static const lean_ctor_object l_Lake_Backend_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lake_Backend_ofString_x3f___closed__3 = (const lean_object*)&l_Lake_Backend_ofString_x3f___closed__3_value;
static const lean_ctor_object l_Lake_Backend_ofString_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_Backend_ofString_x3f___closed__4 = (const lean_object*)&l_Lake_Backend_ofString_x3f___closed__4_value;
static const lean_ctor_object l_Lake_Backend_ofString_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Backend_ofString_x3f___closed__5 = (const lean_object*)&l_Lake_Backend_ofString_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Backend_toString___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Backend_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0 = (const lean_object*)&l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString = (const lean_object*)&l___private_Lake_Config_LeanConfig_0__Lake_Backend_instToString___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_Backend_orPreferLeft(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Backend_orPreferLeft___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedBuildType_default;
LEAN_EXPORT uint8_t l_Lake_instInhabitedBuildType;
static const lean_string_object l_Lake_instReprBuildType_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Lake.BuildType.debug"};
static const lean_object* l_Lake_instReprBuildType_repr___closed__0 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__0_value;
static const lean_ctor_object l_Lake_instReprBuildType_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildType_repr___closed__0_value)}};
static const lean_object* l_Lake_instReprBuildType_repr___closed__1 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__1_value;
static const lean_string_object l_Lake_instReprBuildType_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lake.BuildType.relWithDebInfo"};
static const lean_object* l_Lake_instReprBuildType_repr___closed__2 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__2_value;
static const lean_ctor_object l_Lake_instReprBuildType_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildType_repr___closed__2_value)}};
static const lean_object* l_Lake_instReprBuildType_repr___closed__3 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__3_value;
static const lean_string_object l_Lake_instReprBuildType_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lake.BuildType.minSizeRel"};
static const lean_object* l_Lake_instReprBuildType_repr___closed__4 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__4_value;
static const lean_ctor_object l_Lake_instReprBuildType_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildType_repr___closed__4_value)}};
static const lean_object* l_Lake_instReprBuildType_repr___closed__5 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__5_value;
static const lean_string_object l_Lake_instReprBuildType_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lake.BuildType.release"};
static const lean_object* l_Lake_instReprBuildType_repr___closed__6 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__6_value;
static const lean_ctor_object l_Lake_instReprBuildType_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprBuildType_repr___closed__6_value)}};
static const lean_object* l_Lake_instReprBuildType_repr___closed__7 = (const lean_object*)&l_Lake_instReprBuildType_repr___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprBuildType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprBuildType_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprBuildType___closed__0 = (const lean_object*)&l_Lake_instReprBuildType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprBuildType = (const lean_object*)&l_Lake_instReprBuildType___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_BuildType_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildType(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildType___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instOrdBuildType_ord(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_instOrdBuildType_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instOrdBuildType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instOrdBuildType_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instOrdBuildType___closed__0 = (const lean_object*)&l_Lake_instOrdBuildType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instOrdBuildType = (const lean_object*)&l_Lake_instOrdBuildType___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildType_instLT;
LEAN_EXPORT lean_object* l_Lake_BuildType_instLE;
LEAN_EXPORT uint8_t l_Lake_BuildType_instMin___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_instMin___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_BuildType_instMin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildType_instMin___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildType_instMin___closed__0 = (const lean_object*)&l_Lake_BuildType_instMin___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildType_instMin = (const lean_object*)&l_Lake_BuildType_instMin___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_BuildType_instMax___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_instMax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_BuildType_instMax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildType_instMax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildType_instMax___closed__0 = (const lean_object*)&l_Lake_BuildType_instMax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildType_instMax = (const lean_object*)&l_Lake_BuildType_instMax___closed__0_value;
static const lean_string_object l_Lake_BuildType_leancArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-O0"};
static const lean_object* l_Lake_BuildType_leancArgs___closed__0 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__0_value;
static const lean_string_object l_Lake_BuildType_leancArgs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-g"};
static const lean_object* l_Lake_BuildType_leancArgs___closed__1 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__1_value;
static const lean_array_object l_Lake_BuildType_leancArgs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_BuildType_leancArgs___closed__0_value),((lean_object*)&l_Lake_BuildType_leancArgs___closed__1_value)}};
static const lean_object* l_Lake_BuildType_leancArgs___closed__2 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__2_value;
static const lean_string_object l_Lake_BuildType_leancArgs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-O3"};
static const lean_object* l_Lake_BuildType_leancArgs___closed__3 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__3_value;
static const lean_string_object l_Lake_BuildType_leancArgs___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "-DNDEBUG"};
static const lean_object* l_Lake_BuildType_leancArgs___closed__4 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__4_value;
static const lean_array_object l_Lake_BuildType_leancArgs___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_BuildType_leancArgs___closed__3_value),((lean_object*)&l_Lake_BuildType_leancArgs___closed__1_value),((lean_object*)&l_Lake_BuildType_leancArgs___closed__4_value)}};
static const lean_object* l_Lake_BuildType_leancArgs___closed__5 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__5_value;
static const lean_string_object l_Lake_BuildType_leancArgs___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-Os"};
static const lean_object* l_Lake_BuildType_leancArgs___closed__6 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__6_value;
static const lean_array_object l_Lake_BuildType_leancArgs___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_BuildType_leancArgs___closed__6_value),((lean_object*)&l_Lake_BuildType_leancArgs___closed__4_value)}};
static const lean_object* l_Lake_BuildType_leancArgs___closed__7 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__7_value;
static const lean_array_object l_Lake_BuildType_leancArgs___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_BuildType_leancArgs___closed__3_value),((lean_object*)&l_Lake_BuildType_leancArgs___closed__4_value)}};
static const lean_object* l_Lake_BuildType_leancArgs___closed__8 = (const lean_object*)&l_Lake_BuildType_leancArgs___closed__8_value;
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs___boxed(lean_object*);
static const lean_string_object l_Lake_BuildType_ofString_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__0 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__0_value;
static const lean_string_object l_Lake_BuildType_ofString_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "relWithDebInfo"};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__1 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__1_value;
static const lean_string_object l_Lake_BuildType_ofString_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "minSizeRel"};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__2 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__2_value;
static const lean_string_object l_Lake_BuildType_ofString_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "release"};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__3 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__3_value;
static const lean_ctor_object l_Lake_BuildType_ofString_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__4 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__4_value;
static const lean_ctor_object l_Lake_BuildType_ofString_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__5 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__5_value;
static const lean_ctor_object l_Lake_BuildType_ofString_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__6 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__6_value;
static const lean_ctor_object l_Lake_BuildType_ofString_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_BuildType_ofString_x3f___closed__7 = (const lean_object*)&l_Lake_BuildType_ofString_x3f___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_BuildType_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildType_toString(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_toString___boxed(lean_object*);
static const lean_closure_object l_Lake_BuildType_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_BuildType_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_BuildType_instToString___closed__0 = (const lean_object*)&l_Lake_BuildType_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_BuildType_instToString = (const lean_object*)&l_Lake_BuildType_instToString___closed__0_value;
static const lean_string_object l_Lake_BuildType_leanOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "debugAssertions"};
static const lean_object* l_Lake_BuildType_leanOptions___closed__0 = (const lean_object*)&l_Lake_BuildType_leanOptions___closed__0_value;
static const lean_ctor_object l_Lake_BuildType_leanOptions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_BuildType_leanOptions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 54, 192, 168, 100, 218, 251, 120)}};
static const lean_object* l_Lake_BuildType_leanOptions___closed__1 = (const lean_object*)&l_Lake_BuildType_leanOptions___closed__1_value;
static const lean_ctor_object l_Lake_BuildType_leanOptions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_BuildType_leanOptions___closed__2 = (const lean_object*)&l_Lake_BuildType_leanOptions___closed__2_value;
static lean_once_cell_t l_Lake_BuildType_leanOptions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildType_leanOptions___closed__3;
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions___boxed(lean_object*);
static const lean_array_object l_Lake_BuildType_leanArgs___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildType_leanArgs___redArg___closed__0 = (const lean_object*)&l_Lake_BuildType_leanArgs___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___redArg();
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lake_BuildType_leanArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_BuildType_leanArgs___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___boxed(lean_object*);
static const lean_array_object l_Lake_instInhabitedLeanConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_instInhabitedLeanConfig_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedLeanConfig_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 8, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),((lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 2, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_instInhabitedLeanConfig_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLeanConfig_default = (const lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedLeanConfig = (const lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0 = (const lean_object*)&l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__0_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1 = (const lean_object*)&l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1_value;
static const lean_string_object l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "some "};
static const lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2 = (const lean_object*)&l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value;
static const lean_ctor_object l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__2_value)}};
static const lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3 = (const lean_object*)&l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "#["};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__1_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5;
static lean_once_cell_t l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__4_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8_value;
static const lean_string_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "#[]"};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value;
static const lean_ctor_object l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__9_value)}};
static const lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10 = (const lean_object*)&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10_value;
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object*);
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__0 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__0_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "buildType"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__1 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__1_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__2 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__2_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__3 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__3_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__4 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__4_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__5 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__3_value),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__5_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__6 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__7;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "leanOptions"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__8 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__8_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__9 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__9_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__10;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLeanArgs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__11 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__11_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__11_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__12 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__12_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__13;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "weakLeanArgs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__14 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__14_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__15 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__15_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "moreLeancArgs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__16 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__16_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__17 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__17_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__18;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "moreServerOptions"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__19 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__19_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__19_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__20 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__20_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__21;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "weakLeancArgs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__22 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__22_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__22_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__23 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__23_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLinkObjs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__24 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__24_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__24_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__25 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__25_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLinkLibs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__26 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__26_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__26_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__27 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__27_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "moreLinkArgs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__28 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__28_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__28_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__29 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__29_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "weakLinkArgs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__30 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__30_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__30_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__31 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__31_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "backend"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__32 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__32_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__32_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__33 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__33_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__34;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "platformIndependent"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__35 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__35_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__35_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__36 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__36_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__37;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "precompileImports"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__38 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__39 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__39_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dynlibs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__40 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__41 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__41_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "plugins"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__43 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__43_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "requiresModuleSystem"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__44 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__44_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__44_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__45 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__45_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__46;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "allowNonModules"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__47 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__47_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__47_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__48 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__48_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__49;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__50 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__50_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__51;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__52;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__53 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__53_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__50_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__54 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__54_value;
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lake_instReprLeanConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instReprLeanConfig_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instReprLeanConfig___closed__0 = (const lean_object*)&l_Lake_instReprLeanConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instReprLeanConfig = (const lean_object*)&l_Lake_instReprLeanConfig___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_buildType___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_buildType___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_buildType___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_buildType___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_buildType___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_buildType___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_buildType___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_buildType___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_buildType___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_buildType___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_buildType___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_buildType___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_buildType___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_buildType___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_buildType___proj = (const lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_buildType_instConfigField = (const lean_object*)&l_Lake_LeanConfig_buildType___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_leanOptions___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_leanOptions___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_leanOptions___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_leanOptions___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_leanOptions___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_leanOptions___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_leanOptions___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_leanOptions___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_leanOptions___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_leanOptions___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_leanOptions___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_leanOptions___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_leanOptions___proj = (const lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_leanOptions_instConfigField = (const lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLeanArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLeanArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLeanArgs___proj = (const lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLeanArgs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLeanArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLeanArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_weakLeanArgs___proj = (const lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_weakLeanArgs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_weakLeanArgs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLeancArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLeancArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLeancArgs___proj = (const lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLeancArgs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_moreLeancArgs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreServerOptions___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreServerOptions___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreServerOptions___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreServerOptions___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreServerOptions___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_leanOptions___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_moreServerOptions___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreServerOptions___proj = (const lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreServerOptions_instConfigField = (const lean_object*)&l_Lake_LeanConfig_moreServerOptions___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLeancArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLeancArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_weakLeancArgs___proj = (const lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_weakLeancArgs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_weakLeancArgs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object*, lean_object*);
static const lean_array_object l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0 = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkObjs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkObjs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLinkObjs___proj = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLinkObjs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkLibs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkLibs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLinkLibs___proj = (const lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLinkLibs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_moreLinkLibs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_moreLinkArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLinkArgs___proj = (const lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_moreLinkArgs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_moreLinkArgs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLinkArgs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_weakLinkArgs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLeanArgs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_weakLinkArgs___proj = (const lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_weakLinkArgs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_weakLinkArgs___proj___closed__3_value;
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_backend___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_backend___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_backend___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_backend___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_backend___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_backend___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_backend___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_backend___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_backend___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_backend___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_backend___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_backend___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_backend___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_backend___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_backend___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_backend___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_backend___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_backend___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_backend___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_backend___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_backend___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_backend___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_backend___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_backend___proj = (const lean_object*)&l_Lake_LeanConfig_backend___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_backend_instConfigField = (const lean_object*)&l_Lake_LeanConfig_backend___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_platformIndependent___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_platformIndependent___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_platformIndependent___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_platformIndependent___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_platformIndependent___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_platformIndependent___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_platformIndependent___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_platformIndependent___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_platformIndependent___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_platformIndependent___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_platformIndependent___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_platformIndependent___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_platformIndependent___proj = (const lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_platformIndependent_instConfigField = (const lean_object*)&l_Lake_LeanConfig_platformIndependent___proj___closed__4_value;
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_precompileImports___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_precompileImports___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_precompileImports___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_precompileImports___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_precompileImports___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_precompileImports___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_precompileImports___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_precompileImports___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_precompileImports___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_precompileImports___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_precompileImports___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_precompileImports___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_precompileImports___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_precompileImports___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_precompileImports___proj = (const lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_precompileImports_instConfigField = (const lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_dynlibs___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_dynlibs___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_dynlibs___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_dynlibs___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_dynlibs___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_dynlibs___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_dynlibs___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_dynlibs___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_dynlibs___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_dynlibs___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_dynlibs___proj = (const lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_dynlibs_instConfigField = (const lean_object*)&l_Lake_LeanConfig_dynlibs___proj___closed__3_value;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_plugins___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_plugins___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_plugins___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_plugins___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_plugins___proj___lam__1, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_plugins___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_plugins___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_plugins___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_plugins___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_plugins___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_moreLinkObjs___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_plugins___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_plugins___proj = (const lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_plugins_instConfigField = (const lean_object*)&l_Lake_LeanConfig_plugins___proj___closed__3_value;
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_requiresModuleSystem_instConfigField = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value;
LEAN_EXPORT uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object*, lean_object*);
static const lean_closure_object l_Lake_LeanConfig_allowNonModules___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_allowNonModules___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_allowNonModules___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_allowNonModules___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_allowNonModules___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_allowNonModules___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_allowNonModules___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__2_value;
static const lean_ctor_object l_Lake_LeanConfig_allowNonModules___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_precompileImports___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_allowNonModules___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_allowNonModules___proj = (const lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_allowNonModules_instConfigField = (const lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__3_value;
static const lean_array_object l_Lake_LeanConfig___fields___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_LeanConfig___fields___closed__0 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__0_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 227, 67, 96, 129, 21, 223, 119)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__1 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__1_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__1_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__2 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__2_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__3;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(20, 201, 223, 70, 146, 84, 32, 214)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__4 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__4_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__4_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__4_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__5 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__5_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__6;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__11_value),LEAN_SCALAR_PTR_LITERAL(110, 73, 169, 213, 6, 174, 187, 7)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__7 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__7_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__7_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__7_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__8 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__8_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__9;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__14_value),LEAN_SCALAR_PTR_LITERAL(12, 17, 230, 153, 39, 202, 125, 90)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__10 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__10_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__10_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__10_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__11 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__11_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__12;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(35, 65, 185, 53, 108, 178, 133, 37)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__13 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__13_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__13_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__13_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__14 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__14_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__15;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__19_value),LEAN_SCALAR_PTR_LITERAL(206, 114, 170, 237, 212, 72, 1, 170)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__16 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__16_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__16_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__16_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__17 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__17_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__18;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__22_value),LEAN_SCALAR_PTR_LITERAL(103, 110, 140, 220, 181, 192, 131, 104)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__19 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__19_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__19_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__19_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__20 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__20_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__21;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__24_value),LEAN_SCALAR_PTR_LITERAL(232, 242, 55, 26, 170, 174, 241, 71)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__22 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__22_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__22_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__22_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__23 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__23_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__24;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__26_value),LEAN_SCALAR_PTR_LITERAL(111, 122, 160, 205, 53, 195, 181, 180)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__25 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__25_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__25_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__25_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__26 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__26_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__27;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__28_value),LEAN_SCALAR_PTR_LITERAL(14, 165, 131, 17, 225, 82, 140, 145)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__28 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__28_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__28_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__28_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__29 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__29_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__30;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__30_value),LEAN_SCALAR_PTR_LITERAL(187, 9, 155, 166, 154, 189, 94, 67)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__31 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__31_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__31_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__31_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__32 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__32_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__33;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__32_value),LEAN_SCALAR_PTR_LITERAL(40, 75, 156, 92, 110, 161, 40, 36)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__34 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__34_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__34_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__34_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__35 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__35_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__36;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__35_value),LEAN_SCALAR_PTR_LITERAL(51, 35, 219, 1, 108, 129, 116, 147)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__37 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__37_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__37_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__37_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__38 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__38_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__39;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__38_value),LEAN_SCALAR_PTR_LITERAL(188, 127, 46, 53, 189, 222, 46, 166)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__40 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__40_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__40_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__40_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__41 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__41_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__42;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__40_value),LEAN_SCALAR_PTR_LITERAL(213, 126, 44, 113, 100, 173, 176, 199)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__43 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__43_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__43_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__43_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__44 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__44_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__45;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value),LEAN_SCALAR_PTR_LITERAL(43, 100, 103, 72, 156, 88, 10, 236)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__46 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__46_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__46_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__46_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__47 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__47_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__48;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__44_value),LEAN_SCALAR_PTR_LITERAL(9, 5, 144, 35, 76, 175, 146, 150)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__49 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__49_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__49_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__49_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__50 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__50_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__51;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__47_value),LEAN_SCALAR_PTR_LITERAL(196, 92, 18, 175, 109, 198, 159, 30)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__52 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__52_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__52_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__52_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__53 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__53_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__54;
LEAN_EXPORT lean_object* l_Lake_LeanConfig___fields;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigFields;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_LeanConfig_instConfigInfo___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig_instConfigInfo___closed__0;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__1 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__2 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__3 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__3_value;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__4 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__4_value;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__5 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__5_value;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__6 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__6_value;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__7 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__7_value;
static const lean_ctor_object l_Lake_LeanConfig_instConfigInfo___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__1_value),((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__2_value)}};
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__8 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__8_value;
static const lean_ctor_object l_Lake_LeanConfig_instConfigInfo___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__8_value),((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__3_value),((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__4_value),((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__5_value),((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__6_value)}};
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__9 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__9_value;
static const lean_ctor_object l_Lake_LeanConfig_instConfigInfo___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__9_value),((lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__7_value)}};
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__10 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__10_value;
static lean_once_cell_t l_Lake_LeanConfig_instConfigInfo___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_LeanConfig_instConfigInfo___closed__11;
static lean_once_cell_t l_Lake_LeanConfig_instConfigInfo___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig_instConfigInfo___closed__12;
static const lean_closure_object l_Lake_LeanConfig_instConfigInfo___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_instConfigInfo___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_instConfigInfo___closed__13 = (const lean_object*)&l_Lake_LeanConfig_instConfigInfo___closed__13_value;
static lean_once_cell_t l_Lake_LeanConfig_instConfigInfo___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_LeanConfig_instConfigInfo___closed__14;
static lean_once_cell_t l_Lake_LeanConfig_instConfigInfo___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lake_LeanConfig_instConfigInfo___closed__15;
static lean_once_cell_t l_Lake_LeanConfig_instConfigInfo___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig_instConfigInfo___closed__16;
static lean_once_cell_t l_Lake_LeanConfig_instConfigInfo___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig_instConfigInfo___closed__17;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_instEmptyCollection = (const lean_object*)&l_Lake_instInhabitedLeanConfig_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx___impl___boxed(lean_object* v_x_4_){
_start:
{
uint8_t v_x_4__boxed_5_; lean_object* v_res_6_; 
v_x_4__boxed_5_ = lean_unbox(v_x_4_);
v_res_6_ = l_Lake_Backend_ctorIdx___impl(v_x_4__boxed_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg(lean_object* v_k_7_){
_start:
{
lean_inc(v_k_7_);
return v_k_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg___boxed(lean_object* v_k_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lake_Backend_ctorElim___redArg(v_k_8_);
lean_dec(v_k_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, uint8_t v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
uint8_t v_t_boxed_20_; lean_object* v_res_21_; 
v_t_boxed_20_ = lean_unbox(v_t_17_);
v_res_21_ = l_Lake_Backend_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_boxed_20_, v_h_18_, v_k_19_);
lean_dec(v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg(lean_object* v_c_22_){
_start:
{
lean_inc(v_c_22_);
return v_c_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg___boxed(lean_object* v_c_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lake_Backend_c_elim___redArg(v_c_23_);
lean_dec(v_c_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim(lean_object* v_motive_25_, uint8_t v_t_26_, lean_object* v_h_27_, lean_object* v_c_28_){
_start:
{
lean_inc(v_c_28_);
return v_c_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___boxed(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_c_32_){
_start:
{
uint8_t v_t_boxed_33_; lean_object* v_res_34_; 
v_t_boxed_33_ = lean_unbox(v_t_30_);
v_res_34_ = l_Lake_Backend_c_elim(v_motive_29_, v_t_boxed_33_, v_h_31_, v_c_32_);
lean_dec(v_c_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg(lean_object* v_llvm_35_){
_start:
{
lean_inc(v_llvm_35_);
return v_llvm_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg___boxed(lean_object* v_llvm_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lake_Backend_llvm_elim___redArg(v_llvm_36_);
lean_dec(v_llvm_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim(lean_object* v_motive_38_, uint8_t v_t_39_, lean_object* v_h_40_, lean_object* v_llvm_41_){
_start:
{
lean_inc(v_llvm_41_);
return v_llvm_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___boxed(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_llvm_45_){
_start:
{
uint8_t v_t_boxed_46_; lean_object* v_res_47_; 
v_t_boxed_46_ = lean_unbox(v_t_43_);
v_res_47_ = l_Lake_Backend_llvm_elim(v_motive_42_, v_t_boxed_46_, v_h_44_, v_llvm_45_);
lean_dec(v_llvm_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg(lean_object* v_default_48_){
_start:
{
lean_inc(v_default_48_);
return v_default_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg___boxed(lean_object* v_default_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lake_Backend_default_elim___redArg(v_default_49_);
lean_dec(v_default_49_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim(lean_object* v_motive_51_, uint8_t v_t_52_, lean_object* v_h_53_, lean_object* v_default_54_){
_start:
{
lean_inc(v_default_54_);
return v_default_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___boxed(lean_object* v_motive_55_, lean_object* v_t_56_, lean_object* v_h_57_, lean_object* v_default_58_){
_start:
{
uint8_t v_t_boxed_59_; lean_object* v_res_60_; 
v_t_boxed_59_ = lean_unbox(v_t_56_);
v_res_60_ = l_Lake_Backend_default_elim(v_motive_55_, v_t_boxed_59_, v_h_57_, v_default_58_);
lean_dec(v_default_58_);
return v_res_60_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__6(void){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(2u);
v___x_71_ = lean_nat_to_int(v___x_70_);
return v___x_71_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__7(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_to_int(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr(uint8_t v_x_74_, lean_object* v_prec_75_){
_start:
{
lean_object* v___y_77_; lean_object* v___y_84_; lean_object* v___y_91_; 
switch(v_x_74_)
{
case 0:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_unsigned_to_nat(1024u);
v___x_98_ = lean_nat_dec_le(v___x_97_, v_prec_75_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_77_ = v___x_99_;
goto v___jp_76_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_77_ = v___x_100_;
goto v___jp_76_;
}
}
case 1:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_unsigned_to_nat(1024u);
v___x_102_ = lean_nat_dec_le(v___x_101_, v_prec_75_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_84_ = v___x_103_;
goto v___jp_83_;
}
else
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_84_ = v___x_104_;
goto v___jp_83_;
}
}
default: 
{
lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_105_ = lean_unsigned_to_nat(1024u);
v___x_106_ = lean_nat_dec_le(v___x_105_, v_prec_75_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_91_ = v___x_107_;
goto v___jp_90_;
}
else
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_91_ = v___x_108_;
goto v___jp_90_;
}
}
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__1));
lean_inc(v___y_77_);
v___x_79_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_79_, 0, v___y_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = 0;
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_79_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_80_);
v___x_82_ = l_Repr_addAppParen(v___x_81_, v_prec_75_);
return v___x_82_;
}
v___jp_83_:
{
lean_object* v___x_85_; lean_object* v___x_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_85_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__3));
lean_inc(v___y_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___y_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = 0;
v___x_88_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_88_, sizeof(void*)*1, v___x_87_);
v___x_89_ = l_Repr_addAppParen(v___x_88_, v_prec_75_);
return v___x_89_;
}
v___jp_90_:
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_92_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__5));
lean_inc(v___y_91_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___y_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = 0;
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_94_);
v___x_96_ = l_Repr_addAppParen(v___x_95_, v_prec_75_);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr___boxed(lean_object* v_x_109_, lean_object* v_prec_110_){
_start:
{
uint8_t v_x_171__boxed_111_; lean_object* v_res_112_; 
v_x_171__boxed_111_ = lean_unbox(v_x_109_);
v_res_112_ = l_Lake_instReprBackend_repr(v_x_171__boxed_111_, v_prec_110_);
lean_dec(v_prec_110_);
return v_res_112_;
}
}
LEAN_EXPORT uint8_t l_Lake_Backend_ofNat(lean_object* v_n_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_nat_dec_le(v_n_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(1u);
v___x_119_ = lean_nat_dec_le(v_n_115_, v___x_118_);
if (v___x_119_ == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 2;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 1;
return v___x_121_;
}
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofNat___boxed(lean_object* v_n_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Lake_Backend_ofNat(v_n_123_);
lean_dec(v_n_123_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBackend(uint8_t v_x_126_, uint8_t v_y_127_){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_128_ = lean_box(v_x_126_);
v___x_129_ = lean_obj_tag_nat(v___x_128_);
lean_dec(v___x_128_);
v___x_130_ = lean_box(v_y_127_);
v___x_131_ = lean_obj_tag_nat(v___x_130_);
lean_dec(v___x_130_);
v___x_132_ = lean_nat_dec_eq(v___x_129_, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBackend___boxed(lean_object* v_x_133_, lean_object* v_y_134_){
_start:
{
uint8_t v_x_23__boxed_135_; uint8_t v_y_24__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_x_23__boxed_135_ = lean_unbox(v_x_133_);
v_y_24__boxed_136_ = lean_unbox(v_y_134_);
v_res_137_ = l_Lake_instDecidableEqBackend(v_x_23__boxed_135_, v_y_24__boxed_136_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
static uint8_t _init_l_Lake_Backend_instInhabited(void){
_start:
{
uint8_t v___x_139_; 
v___x_139_ = 2;
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f(lean_object* v_s_152_){
_start:
{
lean_object* v___x_153_; uint8_t v___x_154_; 
v___x_153_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
v___x_154_ = lean_string_dec_eq(v_s_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
v___x_156_ = lean_string_dec_eq(v_s_152_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
v___x_158_ = lean_string_dec_eq(v_s_152_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; 
v___x_159_ = lean_box(0);
return v___x_159_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__3));
return v___x_160_;
}
}
else
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__4));
return v___x_161_;
}
}
else
{
lean_object* v___x_162_; 
v___x_162_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__5));
return v___x_162_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f___boxed(lean_object* v_s_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lake_Backend_ofString_x3f(v_s_163_);
lean_dec_ref(v_s_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_toString(uint8_t v_bt_165_){
_start:
{
switch(v_bt_165_)
{
case 0:
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
return v___x_166_;
}
case 1:
{
lean_object* v___x_167_; 
v___x_167_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
return v___x_167_;
}
default: 
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_toString___boxed(lean_object* v_bt_169_){
_start:
{
uint8_t v_bt_boxed_170_; lean_object* v_res_171_; 
v_bt_boxed_170_ = lean_unbox(v_bt_169_);
v_res_171_ = l_Lake_Backend_toString(v_bt_boxed_170_);
return v_res_171_;
}
}
LEAN_EXPORT uint8_t l_Lake_Backend_orPreferLeft(uint8_t v_x_174_, uint8_t v_x_175_){
_start:
{
if (v_x_174_ == 2)
{
return v_x_175_;
}
else
{
return v_x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_orPreferLeft___boxed(lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
uint8_t v_x_12__boxed_178_; uint8_t v_x_13__boxed_179_; uint8_t v_res_180_; lean_object* v_r_181_; 
v_x_12__boxed_178_ = lean_unbox(v_x_176_);
v_x_13__boxed_179_ = lean_unbox(v_x_177_);
v_res_180_ = l_Lake_Backend_orPreferLeft(v_x_12__boxed_178_, v_x_13__boxed_179_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___impl(uint8_t v_x_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(v_x_182_);
v___x_184_ = lean_obj_tag_nat(v___x_183_);
lean_dec(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___impl___boxed(lean_object* v_x_185_){
_start:
{
uint8_t v_x_4__boxed_186_; lean_object* v_res_187_; 
v_x_4__boxed_186_ = lean_unbox(v_x_185_);
v_res_187_ = l_Lake_BuildType_ctorIdx___impl(v_x_4__boxed_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg(lean_object* v_k_188_){
_start:
{
lean_inc(v_k_188_);
return v_k_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg___boxed(lean_object* v_k_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lake_BuildType_ctorElim___redArg(v_k_189_);
lean_dec(v_k_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim(lean_object* v_motive_191_, lean_object* v_ctorIdx_192_, uint8_t v_t_193_, lean_object* v_h_194_, lean_object* v_k_195_){
_start:
{
lean_inc(v_k_195_);
return v_k_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___boxed(lean_object* v_motive_196_, lean_object* v_ctorIdx_197_, lean_object* v_t_198_, lean_object* v_h_199_, lean_object* v_k_200_){
_start:
{
uint8_t v_t_boxed_201_; lean_object* v_res_202_; 
v_t_boxed_201_ = lean_unbox(v_t_198_);
v_res_202_ = l_Lake_BuildType_ctorElim(v_motive_196_, v_ctorIdx_197_, v_t_boxed_201_, v_h_199_, v_k_200_);
lean_dec(v_k_200_);
lean_dec(v_ctorIdx_197_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg(lean_object* v_debug_203_){
_start:
{
lean_inc(v_debug_203_);
return v_debug_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg___boxed(lean_object* v_debug_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lake_BuildType_debug_elim___redArg(v_debug_204_);
lean_dec(v_debug_204_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim(lean_object* v_motive_206_, uint8_t v_t_207_, lean_object* v_h_208_, lean_object* v_debug_209_){
_start:
{
lean_inc(v_debug_209_);
return v_debug_209_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___boxed(lean_object* v_motive_210_, lean_object* v_t_211_, lean_object* v_h_212_, lean_object* v_debug_213_){
_start:
{
uint8_t v_t_boxed_214_; lean_object* v_res_215_; 
v_t_boxed_214_ = lean_unbox(v_t_211_);
v_res_215_ = l_Lake_BuildType_debug_elim(v_motive_210_, v_t_boxed_214_, v_h_212_, v_debug_213_);
lean_dec(v_debug_213_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg(lean_object* v_relWithDebInfo_216_){
_start:
{
lean_inc(v_relWithDebInfo_216_);
return v_relWithDebInfo_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg___boxed(lean_object* v_relWithDebInfo_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lake_BuildType_relWithDebInfo_elim___redArg(v_relWithDebInfo_217_);
lean_dec(v_relWithDebInfo_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim(lean_object* v_motive_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_relWithDebInfo_222_){
_start:
{
lean_inc(v_relWithDebInfo_222_);
return v_relWithDebInfo_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_relWithDebInfo_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lake_BuildType_relWithDebInfo_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_relWithDebInfo_226_);
lean_dec(v_relWithDebInfo_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg(lean_object* v_minSizeRel_229_){
_start:
{
lean_inc(v_minSizeRel_229_);
return v_minSizeRel_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg___boxed(lean_object* v_minSizeRel_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_BuildType_minSizeRel_elim___redArg(v_minSizeRel_230_);
lean_dec(v_minSizeRel_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_minSizeRel_235_){
_start:
{
lean_inc(v_minSizeRel_235_);
return v_minSizeRel_235_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_minSizeRel_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lake_BuildType_minSizeRel_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_minSizeRel_239_);
lean_dec(v_minSizeRel_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg(lean_object* v_release_242_){
_start:
{
lean_inc(v_release_242_);
return v_release_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg___boxed(lean_object* v_release_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lake_BuildType_release_elim___redArg(v_release_243_);
lean_dec(v_release_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_release_248_){
_start:
{
lean_inc(v_release_248_);
return v_release_248_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_release_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lake_BuildType_release_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_release_252_);
lean_dec(v_release_252_);
return v_res_254_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType_default(void){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = 0;
return v___x_255_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType(void){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr(uint8_t v_x_269_, lean_object* v_prec_270_){
_start:
{
lean_object* v___y_272_; lean_object* v___y_279_; lean_object* v___y_286_; lean_object* v___y_293_; 
switch(v_x_269_)
{
case 0:
{
lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1024u);
v___x_300_ = lean_nat_dec_le(v___x_299_, v_prec_270_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_272_ = v___x_301_;
goto v___jp_271_;
}
else
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_272_ = v___x_302_;
goto v___jp_271_;
}
}
case 1:
{
lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_nat_dec_le(v___x_303_, v_prec_270_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_279_ = v___x_305_;
goto v___jp_278_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_279_ = v___x_306_;
goto v___jp_278_;
}
}
case 2:
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1024u);
v___x_308_ = lean_nat_dec_le(v___x_307_, v_prec_270_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
v___x_309_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_286_ = v___x_309_;
goto v___jp_285_;
}
else
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_286_ = v___x_310_;
goto v___jp_285_;
}
}
default: 
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1024u);
v___x_312_ = lean_nat_dec_le(v___x_311_, v_prec_270_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_293_ = v___x_313_;
goto v___jp_292_;
}
else
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_293_ = v___x_314_;
goto v___jp_292_;
}
}
}
v___jp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_273_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__1));
lean_inc(v___y_272_);
v___x_274_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_274_, 0, v___y_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = 0;
v___x_276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_276_, 0, v___x_274_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_275_);
v___x_277_ = l_Repr_addAppParen(v___x_276_, v_prec_270_);
return v___x_277_;
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_280_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__3));
lean_inc(v___y_279_);
v___x_281_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_281_, 0, v___y_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = 0;
v___x_283_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set_uint8(v___x_283_, sizeof(void*)*1, v___x_282_);
v___x_284_ = l_Repr_addAppParen(v___x_283_, v_prec_270_);
return v___x_284_;
}
v___jp_285_:
{
lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_287_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__5));
lean_inc(v___y_286_);
v___x_288_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_288_, 0, v___y_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___x_289_ = 0;
v___x_290_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set_uint8(v___x_290_, sizeof(void*)*1, v___x_289_);
v___x_291_ = l_Repr_addAppParen(v___x_290_, v_prec_270_);
return v___x_291_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_294_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__7));
lean_inc(v___y_293_);
v___x_295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_295_, 0, v___y_293_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = 0;
v___x_297_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1, v___x_296_);
v___x_298_ = l_Repr_addAppParen(v___x_297_, v_prec_270_);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr___boxed(lean_object* v_x_315_, lean_object* v_prec_316_){
_start:
{
uint8_t v_x_221__boxed_317_; lean_object* v_res_318_; 
v_x_221__boxed_317_ = lean_unbox(v_x_315_);
v_res_318_ = l_Lake_instReprBuildType_repr(v_x_221__boxed_317_, v_prec_316_);
lean_dec(v_prec_316_);
return v_res_318_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_ofNat(lean_object* v_n_321_){
_start:
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_dec_le(v_n_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(2u);
v___x_325_ = lean_nat_dec_le(v_n_321_, v___x_324_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
v___x_326_ = 3;
return v___x_326_;
}
else
{
uint8_t v___x_327_; 
v___x_327_ = 2;
return v___x_327_;
}
}
else
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_nat_dec_le(v_n_321_, v___x_328_);
if (v___x_329_ == 0)
{
uint8_t v___x_330_; 
v___x_330_ = 1;
return v___x_330_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = 0;
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofNat___boxed(lean_object* v_n_332_){
_start:
{
uint8_t v_res_333_; lean_object* v_r_334_; 
v_res_333_ = l_Lake_BuildType_ofNat(v_n_332_);
lean_dec(v_n_332_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildType(uint8_t v_x_335_, uint8_t v_y_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_337_ = lean_box(v_x_335_);
v___x_338_ = lean_obj_tag_nat(v___x_337_);
lean_dec(v___x_337_);
v___x_339_ = lean_box(v_y_336_);
v___x_340_ = lean_obj_tag_nat(v___x_339_);
lean_dec(v___x_339_);
v___x_341_ = lean_nat_dec_eq(v___x_338_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildType___boxed(lean_object* v_x_342_, lean_object* v_y_343_){
_start:
{
uint8_t v_x_23__boxed_344_; uint8_t v_y_24__boxed_345_; uint8_t v_res_346_; lean_object* v_r_347_; 
v_x_23__boxed_344_ = lean_unbox(v_x_342_);
v_y_24__boxed_345_ = lean_unbox(v_y_343_);
v_res_346_ = l_Lake_instDecidableEqBuildType(v_x_23__boxed_344_, v_y_24__boxed_345_);
v_r_347_ = lean_box(v_res_346_);
return v_r_347_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdBuildType_ord(uint8_t v_x_348_, uint8_t v_y_349_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; uint8_t v___x_354_; 
v___x_350_ = lean_box(v_x_348_);
v___x_351_ = lean_obj_tag_nat(v___x_350_);
lean_dec(v___x_350_);
v___x_352_ = lean_box(v_y_349_);
v___x_353_ = lean_obj_tag_nat(v___x_352_);
lean_dec(v___x_352_);
v___x_354_ = lean_nat_dec_lt(v___x_351_, v___x_353_);
if (v___x_354_ == 0)
{
uint8_t v___x_355_; 
v___x_355_ = lean_nat_dec_eq(v___x_351_, v___x_353_);
if (v___x_355_ == 0)
{
uint8_t v___x_356_; 
v___x_356_ = 2;
return v___x_356_;
}
else
{
uint8_t v___x_357_; 
v___x_357_ = 1;
return v___x_357_;
}
}
else
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdBuildType_ord___boxed(lean_object* v_x_359_, lean_object* v_y_360_){
_start:
{
uint8_t v_x_33__boxed_361_; uint8_t v_y_34__boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v_x_33__boxed_361_ = lean_unbox(v_x_359_);
v_y_34__boxed_362_ = lean_unbox(v_y_360_);
v_res_363_ = l_Lake_instOrdBuildType_ord(v_x_33__boxed_361_, v_y_34__boxed_362_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
static lean_object* _init_l_Lake_BuildType_instLT(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_box(0);
return v___x_367_;
}
}
static lean_object* _init_l_Lake_BuildType_instLE(void){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_box(0);
return v___x_368_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_instMin___lam__0(uint8_t v_x_369_, uint8_t v_y_370_){
_start:
{
uint8_t v___x_371_; 
v___x_371_ = l_Lake_instOrdBuildType_ord(v_x_369_, v_y_370_);
if (v___x_371_ == 2)
{
return v_y_370_;
}
else
{
return v_x_369_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMin___lam__0___boxed(lean_object* v_x_372_, lean_object* v_y_373_){
_start:
{
uint8_t v_x_boxed_374_; uint8_t v_y_boxed_375_; uint8_t v_res_376_; lean_object* v_r_377_; 
v_x_boxed_374_ = lean_unbox(v_x_372_);
v_y_boxed_375_ = lean_unbox(v_y_373_);
v_res_376_ = l_Lake_BuildType_instMin___lam__0(v_x_boxed_374_, v_y_boxed_375_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_instMax___lam__0(uint8_t v_x_380_, uint8_t v_y_381_){
_start:
{
uint8_t v___x_382_; 
v___x_382_ = l_Lake_instOrdBuildType_ord(v_x_380_, v_y_381_);
if (v___x_382_ == 2)
{
return v_x_380_;
}
else
{
return v_y_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMax___lam__0___boxed(lean_object* v_x_383_, lean_object* v_y_384_){
_start:
{
uint8_t v_x_boxed_385_; uint8_t v_y_boxed_386_; uint8_t v_res_387_; lean_object* v_r_388_; 
v_x_boxed_385_ = lean_unbox(v_x_383_);
v_y_boxed_386_ = lean_unbox(v_y_384_);
v_res_387_ = l_Lake_BuildType_instMax___lam__0(v_x_boxed_385_, v_y_boxed_386_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs(uint8_t v_x_422_){
_start:
{
switch(v_x_422_)
{
case 0:
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__2));
return v___x_423_;
}
case 1:
{
lean_object* v___x_424_; 
v___x_424_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__5));
return v___x_424_;
}
case 2:
{
lean_object* v___x_425_; 
v___x_425_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__7));
return v___x_425_;
}
default: 
{
lean_object* v___x_426_; 
v___x_426_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__8));
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs___boxed(lean_object* v_x_427_){
_start:
{
uint8_t v_x_163__boxed_428_; lean_object* v_res_429_; 
v_x_163__boxed_428_ = lean_unbox(v_x_427_);
v_res_429_ = l_Lake_BuildType_leancArgs(v_x_163__boxed_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofString_x3f(lean_object* v_s_446_){
_start:
{
lean_object* v___y_448_; lean_object* v___x_462_; uint32_t v___x_463_; uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_string_utf8_get(v_s_446_, v___x_462_);
v___x_464_ = 65;
v___x_465_ = lean_uint32_dec_le(v___x_464_, v___x_463_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_string_utf8_set(v_s_446_, v___x_462_, v___x_463_);
v___y_448_ = v___x_466_;
goto v___jp_447_;
}
else
{
uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_467_ = 90;
v___x_468_ = lean_uint32_dec_le(v___x_463_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
v___x_469_ = lean_string_utf8_set(v_s_446_, v___x_462_, v___x_463_);
v___y_448_ = v___x_469_;
goto v___jp_447_;
}
else
{
uint32_t v___x_470_; uint32_t v___x_471_; lean_object* v___x_472_; 
v___x_470_ = 32;
v___x_471_ = lean_uint32_add(v___x_463_, v___x_470_);
v___x_472_ = lean_string_utf8_set(v_s_446_, v___x_462_, v___x_471_);
v___y_448_ = v___x_472_;
goto v___jp_447_;
}
}
v___jp_447_:
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
v___x_450_ = lean_string_dec_eq(v___y_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_451_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
v___x_452_ = lean_string_dec_eq(v___y_448_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
v___x_454_ = lean_string_dec_eq(v___y_448_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
v___x_456_ = lean_string_dec_eq(v___y_448_, v___x_455_);
lean_dec_ref(v___y_448_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
lean_object* v___x_458_; 
v___x_458_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__4));
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; 
lean_dec_ref(v___y_448_);
v___x_459_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__5));
return v___x_459_;
}
}
else
{
lean_object* v___x_460_; 
lean_dec_ref(v___y_448_);
v___x_460_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__6));
return v___x_460_;
}
}
else
{
lean_object* v___x_461_; 
lean_dec_ref(v___y_448_);
v___x_461_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__7));
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString(uint8_t v_bt_473_){
_start:
{
switch(v_bt_473_)
{
case 0:
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
return v___x_474_;
}
case 1:
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
return v___x_475_;
}
case 2:
{
lean_object* v___x_476_; 
v___x_476_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
return v___x_476_;
}
default: 
{
lean_object* v___x_477_; 
v___x_477_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString___boxed(lean_object* v_bt_478_){
_start:
{
uint8_t v_bt_boxed_479_; lean_object* v_res_480_; 
v_bt_boxed_479_ = lean_unbox(v_bt_478_);
v_res_480_ = l_Lake_BuildType_toString(v_bt_boxed_479_);
return v_res_480_;
}
}
static lean_object* _init_l_Lake_BuildType_leanOptions___closed__3(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = lean_box(1);
v___x_489_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__2));
v___x_490_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__1));
v___x_491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_490_, v___x_489_, v___x_488_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions(uint8_t v_x_492_){
_start:
{
if (v_x_492_ == 0)
{
lean_object* v___x_493_; 
v___x_493_ = lean_obj_once(&l_Lake_BuildType_leanOptions___closed__3, &l_Lake_BuildType_leanOptions___closed__3_once, _init_l_Lake_BuildType_leanOptions___closed__3);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = lean_box(1);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions___boxed(lean_object* v_x_495_){
_start:
{
uint8_t v_x_66__boxed_496_; lean_object* v_res_497_; 
v_x_66__boxed_496_ = lean_unbox(v_x_495_);
v_res_497_ = l_Lake_BuildType_leanOptions(v_x_66__boxed_496_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___redArg(){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l_Lake_BuildType_leanArgs___redArg___closed__0));
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___redArg___boxed(lean_object* v___dummy_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lake_BuildType_leanArgs___redArg();
return v_res_503_;
}
}
static lean_object* _init_l_Lake_BuildType_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs(uint8_t v_t_505_){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = lean_obj_once(&l_Lake_BuildType_leanArgs___closed__0, &l_Lake_BuildType_leanArgs___closed__0_once, _init_l_Lake_BuildType_leanArgs___closed__0);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___boxed(lean_object* v_t_507_){
_start:
{
uint8_t v_t_boxed_508_; lean_object* v_res_509_; 
v_t_boxed_508_ = lean_unbox(v_t_507_);
v_res_509_ = l_Lake_BuildType_leanArgs(v_t_boxed_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1));
return v___x_528_;
}
else
{
lean_object* v_val_529_; lean_object* v___x_530_; uint8_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_val_529_ = lean_ctor_get(v_x_526_, 0);
v___x_530_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3));
v___x_531_ = lean_unbox(v_val_529_);
v___x_532_ = l_Bool_repr___redArg(v___x_531_);
v___x_533_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_530_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = l_Repr_addAppParen(v___x_533_, v_x_527_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_535_, v_x_536_);
lean_dec(v_x_536_);
lean_dec(v_x_535_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object* v_a_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = lean_nat_to_int(v_a_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object* v___y_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = l_String_quote(v___y_540_);
v___x_542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_dec(v_x_543_);
return v_x_544_;
}
else
{
lean_object* v_head_546_; lean_object* v_tail_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_558_; 
v_head_546_ = lean_ctor_get(v_x_545_, 0);
v_tail_547_ = lean_ctor_get(v_x_545_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_558_ == 0)
{
v___x_549_ = v_x_545_;
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_tail_547_);
lean_inc(v_head_546_);
lean_dec(v_x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_558_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
lean_inc(v_x_543_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 5);
lean_ctor_set(v___x_549_, 1, v_x_543_);
lean_ctor_set(v___x_549_, 0, v_x_544_);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_x_544_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v_x_543_);
v___x_552_ = v_reuseFailAlloc_557_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = l_String_quote(v_head_546_);
v___x_554_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
v___x_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_552_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v_x_544_ = v___x_555_;
v_x_545_ = v_tail_547_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_dec(v_x_559_);
return v_x_560_;
}
else
{
lean_object* v_head_562_; lean_object* v_tail_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_574_; 
v_head_562_ = lean_ctor_get(v_x_561_, 0);
v_tail_563_ = lean_ctor_get(v_x_561_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_574_ == 0)
{
v___x_565_ = v_x_561_;
v_isShared_566_ = v_isSharedCheck_574_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_tail_563_);
lean_inc(v_head_562_);
lean_dec(v_x_561_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_574_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_568_; 
lean_inc(v_x_559_);
if (v_isShared_566_ == 0)
{
lean_ctor_set_tag(v___x_565_, 5);
lean_ctor_set(v___x_565_, 1, v_x_559_);
lean_ctor_set(v___x_565_, 0, v_x_560_);
v___x_568_ = v___x_565_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_x_560_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_x_559_);
v___x_568_ = v_reuseFailAlloc_573_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_569_ = l_String_quote(v_head_562_);
v___x_570_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
v___x_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_568_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_559_, v___x_571_, v_tail_563_);
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
if (lean_obj_tag(v_x_575_) == 0)
{
lean_object* v___x_577_; 
lean_dec(v_x_576_);
v___x_577_ = lean_box(0);
return v___x_577_;
}
else
{
lean_object* v_tail_578_; 
v_tail_578_ = lean_ctor_get(v_x_575_, 1);
if (lean_obj_tag(v_tail_578_) == 0)
{
lean_object* v_head_579_; lean_object* v___x_580_; 
lean_dec(v_x_576_);
v_head_579_ = lean_ctor_get(v_x_575_, 0);
lean_inc(v_head_579_);
lean_dec_ref_known(v_x_575_, 2);
v___x_580_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_579_);
return v___x_580_;
}
else
{
lean_object* v_head_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
lean_inc(v_tail_578_);
v_head_581_ = lean_ctor_get(v_x_575_, 0);
lean_inc(v_head_581_);
lean_dec_ref_known(v_x_575_, 2);
v___x_582_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_581_);
v___x_583_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_576_, v___x_582_, v_tail_578_);
return v___x_583_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0));
v___x_593_ = lean_string_length(v___x_592_);
return v___x_593_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5);
v___x_595_ = lean_nat_to_int(v___x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object* v_xs_603_){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = lean_array_get_size(v_xs_603_);
v___x_605_ = lean_unsigned_to_nat(0u);
v___x_606_ = lean_nat_dec_eq(v___x_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_607_ = lean_array_to_list(v_xs_603_);
v___x_608_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_609_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_607_, v___x_608_);
v___x_610_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_611_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v___x_609_);
v___x_613_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
v___x_615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_610_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Std_Format_fill(v___x_615_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; 
lean_dec_ref(v_xs_603_);
v___x_617_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object* v___y_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = l_Lake_Target_repr___redArg(v___y_618_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
if (lean_obj_tag(v_x_623_) == 0)
{
lean_dec(v_x_621_);
return v_x_622_;
}
else
{
lean_object* v_head_624_; lean_object* v_tail_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_636_; 
v_head_624_ = lean_ctor_get(v_x_623_, 0);
v_tail_625_ = lean_ctor_get(v_x_623_, 1);
v_isSharedCheck_636_ = !lean_is_exclusive(v_x_623_);
if (v_isSharedCheck_636_ == 0)
{
v___x_627_ = v_x_623_;
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_tail_625_);
lean_inc(v_head_624_);
lean_dec(v_x_623_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
lean_inc(v_x_621_);
if (v_isShared_628_ == 0)
{
lean_ctor_set_tag(v___x_627_, 5);
lean_ctor_set(v___x_627_, 1, v_x_621_);
lean_ctor_set(v___x_627_, 0, v_x_622_);
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_x_622_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_x_621_);
v___x_630_ = v_reuseFailAlloc_635_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = l_Lake_Target_repr___redArg(v_head_624_, v___x_631_);
v___x_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_630_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v_x_622_ = v___x_633_;
v_x_623_ = v_tail_625_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_639_) == 0)
{
lean_dec(v_x_637_);
return v_x_638_;
}
else
{
lean_object* v_head_640_; lean_object* v_tail_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_652_; 
v_head_640_ = lean_ctor_get(v_x_639_, 0);
v_tail_641_ = lean_ctor_get(v_x_639_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_x_639_);
if (v_isSharedCheck_652_ == 0)
{
v___x_643_ = v_x_639_;
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_tail_641_);
lean_inc(v_head_640_);
lean_dec(v_x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_652_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
lean_inc(v_x_637_);
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 5);
lean_ctor_set(v___x_643_, 1, v_x_637_);
lean_ctor_set(v___x_643_, 0, v_x_638_);
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_x_638_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_x_637_);
v___x_646_ = v_reuseFailAlloc_651_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = l_Lake_Target_repr___redArg(v_head_640_, v___x_647_);
v___x_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_646_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_637_, v___x_649_, v_tail_641_);
return v___x_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
lean_object* v___x_655_; 
lean_dec(v_x_654_);
v___x_655_ = lean_box(0);
return v___x_655_;
}
else
{
lean_object* v_tail_656_; 
v_tail_656_ = lean_ctor_get(v_x_653_, 1);
if (lean_obj_tag(v_tail_656_) == 0)
{
lean_object* v_head_657_; lean_object* v___x_658_; 
lean_dec(v_x_654_);
v_head_657_ = lean_ctor_get(v_x_653_, 0);
lean_inc(v_head_657_);
lean_dec_ref_known(v_x_653_, 2);
v___x_658_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_657_);
return v___x_658_;
}
else
{
lean_object* v_head_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
lean_inc(v_tail_656_);
v_head_659_ = lean_ctor_get(v_x_653_, 0);
lean_inc(v_head_659_);
lean_dec_ref_known(v_x_653_, 2);
v___x_660_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_659_);
v___x_661_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_654_, v___x_660_, v_tail_656_);
return v___x_661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object* v_xs_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_array_get_size(v_xs_662_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_nat_dec_eq(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_666_ = lean_array_to_list(v_xs_662_);
v___x_667_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_668_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_666_, v___x_667_);
v___x_669_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_670_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v___x_668_);
v___x_672_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_669_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = l_Std_Format_fill(v___x_674_);
return v___x_675_;
}
else
{
lean_object* v___x_676_; 
lean_dec_ref(v_xs_662_);
v___x_676_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
if (lean_obj_tag(v_x_679_) == 0)
{
lean_dec(v_x_677_);
return v_x_678_;
}
else
{
lean_object* v_head_680_; lean_object* v_tail_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_691_; 
v_head_680_ = lean_ctor_get(v_x_679_, 0);
v_tail_681_ = lean_ctor_get(v_x_679_, 1);
v_isSharedCheck_691_ = !lean_is_exclusive(v_x_679_);
if (v_isSharedCheck_691_ == 0)
{
v___x_683_ = v_x_679_;
v_isShared_684_ = v_isSharedCheck_691_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_tail_681_);
lean_inc(v_head_680_);
lean_dec(v_x_679_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_691_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
lean_inc(v_x_677_);
if (v_isShared_684_ == 0)
{
lean_ctor_set_tag(v___x_683_, 5);
lean_ctor_set(v___x_683_, 1, v_x_677_);
lean_ctor_set(v___x_683_, 0, v_x_678_);
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v_x_678_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_x_677_);
v___x_686_ = v_reuseFailAlloc_690_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = l_Lean_instReprLeanOption_repr___redArg(v_head_680_);
v___x_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_686_);
lean_ctor_set(v___x_688_, 1, v___x_687_);
v_x_678_ = v___x_688_;
v_x_679_ = v_tail_681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_694_) == 0)
{
lean_dec(v_x_692_);
return v_x_693_;
}
else
{
lean_object* v_head_695_; lean_object* v_tail_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
v_head_695_ = lean_ctor_get(v_x_694_, 0);
v_tail_696_ = lean_ctor_get(v_x_694_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v_x_694_);
if (v_isSharedCheck_706_ == 0)
{
v___x_698_ = v_x_694_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_tail_696_);
lean_inc(v_head_695_);
lean_dec(v_x_694_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
lean_inc(v_x_692_);
if (v_isShared_699_ == 0)
{
lean_ctor_set_tag(v___x_698_, 5);
lean_ctor_set(v___x_698_, 1, v_x_692_);
lean_ctor_set(v___x_698_, 0, v_x_693_);
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_x_693_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_x_692_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = l_Lean_instReprLeanOption_repr___redArg(v_head_695_);
v___x_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_701_);
lean_ctor_set(v___x_703_, 1, v___x_702_);
v___x_704_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_692_, v___x_703_, v_tail_696_);
return v___x_704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object* v_x_707_, lean_object* v_x_708_){
_start:
{
if (lean_obj_tag(v_x_707_) == 0)
{
lean_object* v___x_709_; 
lean_dec(v_x_708_);
v___x_709_ = lean_box(0);
return v___x_709_;
}
else
{
lean_object* v_tail_710_; 
v_tail_710_ = lean_ctor_get(v_x_707_, 1);
if (lean_obj_tag(v_tail_710_) == 0)
{
lean_object* v_head_711_; lean_object* v___x_712_; 
lean_dec(v_x_708_);
v_head_711_ = lean_ctor_get(v_x_707_, 0);
lean_inc(v_head_711_);
lean_dec_ref_known(v_x_707_, 2);
v___x_712_ = l_Lean_instReprLeanOption_repr___redArg(v_head_711_);
return v___x_712_;
}
else
{
lean_object* v_head_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_inc(v_tail_710_);
v_head_713_ = lean_ctor_get(v_x_707_, 0);
lean_inc(v_head_713_);
lean_dec_ref_known(v_x_707_, 2);
v___x_714_ = l_Lean_instReprLeanOption_repr___redArg(v_head_713_);
v___x_715_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_708_, v___x_714_, v_tail_710_);
return v___x_715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object* v_xs_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = lean_array_get_size(v_xs_716_);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = lean_nat_dec_eq(v___x_717_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_720_ = lean_array_to_list(v_xs_716_);
v___x_721_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_722_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_720_, v___x_721_);
v___x_723_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_724_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_722_);
v___x_726_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
v___x_728_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_723_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Std_Format_fill(v___x_728_);
return v___x_729_;
}
else
{
lean_object* v___x_730_; 
lean_dec_ref(v_xs_716_);
v___x_730_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
lean_dec(v_x_731_);
return v_x_732_;
}
else
{
lean_object* v_head_734_; lean_object* v_tail_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_746_; 
v_head_734_ = lean_ctor_get(v_x_733_, 0);
v_tail_735_ = lean_ctor_get(v_x_733_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_746_ == 0)
{
v___x_737_ = v_x_733_;
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_tail_735_);
lean_inc(v_head_734_);
lean_dec(v_x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_746_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
lean_inc(v_x_731_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 5);
lean_ctor_set(v___x_737_, 1, v_x_731_);
lean_ctor_set(v___x_737_, 0, v_x_732_);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_x_732_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_x_731_);
v___x_740_ = v_reuseFailAlloc_745_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = l_Lake_Target_repr___redArg(v_head_734_, v___x_741_);
v___x_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_740_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
v_x_732_ = v___x_743_;
v_x_733_ = v_tail_735_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
if (lean_obj_tag(v_x_749_) == 0)
{
lean_dec(v_x_747_);
return v_x_748_;
}
else
{
lean_object* v_head_750_; lean_object* v_tail_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_762_; 
v_head_750_ = lean_ctor_get(v_x_749_, 0);
v_tail_751_ = lean_ctor_get(v_x_749_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_762_ == 0)
{
v___x_753_ = v_x_749_;
v_isShared_754_ = v_isSharedCheck_762_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_tail_751_);
lean_inc(v_head_750_);
lean_dec(v_x_749_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_762_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
lean_inc(v_x_747_);
if (v_isShared_754_ == 0)
{
lean_ctor_set_tag(v___x_753_, 5);
lean_ctor_set(v___x_753_, 1, v_x_747_);
lean_ctor_set(v___x_753_, 0, v_x_748_);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_x_748_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_x_747_);
v___x_756_ = v_reuseFailAlloc_761_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_757_ = lean_unsigned_to_nat(0u);
v___x_758_ = l_Lake_Target_repr___redArg(v_head_750_, v___x_757_);
v___x_759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_756_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_747_, v___x_759_, v_tail_751_);
return v___x_760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object* v_x_763_, lean_object* v_x_764_){
_start:
{
if (lean_obj_tag(v_x_763_) == 0)
{
lean_object* v___x_765_; 
lean_dec(v_x_764_);
v___x_765_ = lean_box(0);
return v___x_765_;
}
else
{
lean_object* v_tail_766_; 
v_tail_766_ = lean_ctor_get(v_x_763_, 1);
if (lean_obj_tag(v_tail_766_) == 0)
{
lean_object* v_head_767_; lean_object* v___x_768_; 
lean_dec(v_x_764_);
v_head_767_ = lean_ctor_get(v_x_763_, 0);
lean_inc(v_head_767_);
lean_dec_ref_known(v_x_763_, 2);
v___x_768_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_767_);
return v___x_768_;
}
else
{
lean_object* v_head_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
lean_inc(v_tail_766_);
v_head_769_ = lean_ctor_get(v_x_763_, 0);
lean_inc(v_head_769_);
lean_dec_ref_known(v_x_763_, 2);
v___x_770_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_769_);
v___x_771_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_764_, v___x_770_, v_tail_766_);
return v___x_771_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object* v_xs_772_){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_array_get_size(v_xs_772_);
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = lean_nat_dec_eq(v___x_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_776_ = lean_array_to_list(v_xs_772_);
v___x_777_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_778_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_776_, v___x_777_);
v___x_779_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_780_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___x_778_);
v___x_782_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_779_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Std_Format_fill(v___x_784_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; 
lean_dec_ref(v_xs_772_);
v___x_786_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_786_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(13u);
v___x_801_ = lean_nat_to_int(v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_unsigned_to_nat(15u);
v___x_806_ = lean_nat_to_int(v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(16u);
v___x_811_ = lean_nat_to_int(v___x_810_);
return v___x_811_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_unsigned_to_nat(17u);
v___x_819_ = lean_nat_to_int(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(21u);
v___x_824_ = lean_nat_to_int(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = lean_unsigned_to_nat(11u);
v___x_844_ = lean_nat_to_int(v___x_843_);
return v___x_844_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_unsigned_to_nat(23u);
v___x_849_ = lean_nat_to_int(v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(24u);
v___x_863_ = lean_nat_to_int(v___x_862_);
return v___x_863_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = lean_unsigned_to_nat(19u);
v___x_868_ = lean_nat_to_int(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_871_ = lean_string_length(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__51, &l_Lake_instReprLeanConfig_repr___redArg___closed__51_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51);
v___x_873_ = lean_nat_to_int(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_878_){
_start:
{
uint8_t v_buildType_879_; lean_object* v_leanOptions_880_; lean_object* v_moreLeanArgs_881_; lean_object* v_weakLeanArgs_882_; lean_object* v_moreLeancArgs_883_; lean_object* v_moreServerOptions_884_; lean_object* v_weakLeancArgs_885_; lean_object* v_moreLinkObjs_886_; lean_object* v_moreLinkLibs_887_; lean_object* v_moreLinkArgs_888_; lean_object* v_weakLinkArgs_889_; uint8_t v_backend_890_; lean_object* v_platformIndependent_891_; uint8_t v_precompileImports_892_; lean_object* v_dynlibs_893_; lean_object* v_plugins_894_; uint8_t v_requiresModuleSystem_895_; uint8_t v_allowNonModules_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_buildType_879_ = lean_ctor_get_uint8(v_x_878_, sizeof(void*)*13);
v_leanOptions_880_ = lean_ctor_get(v_x_878_, 0);
lean_inc_ref(v_leanOptions_880_);
v_moreLeanArgs_881_ = lean_ctor_get(v_x_878_, 1);
lean_inc_ref(v_moreLeanArgs_881_);
v_weakLeanArgs_882_ = lean_ctor_get(v_x_878_, 2);
lean_inc_ref(v_weakLeanArgs_882_);
v_moreLeancArgs_883_ = lean_ctor_get(v_x_878_, 3);
lean_inc_ref(v_moreLeancArgs_883_);
v_moreServerOptions_884_ = lean_ctor_get(v_x_878_, 4);
lean_inc_ref(v_moreServerOptions_884_);
v_weakLeancArgs_885_ = lean_ctor_get(v_x_878_, 5);
lean_inc_ref(v_weakLeancArgs_885_);
v_moreLinkObjs_886_ = lean_ctor_get(v_x_878_, 6);
lean_inc_ref(v_moreLinkObjs_886_);
v_moreLinkLibs_887_ = lean_ctor_get(v_x_878_, 7);
lean_inc_ref(v_moreLinkLibs_887_);
v_moreLinkArgs_888_ = lean_ctor_get(v_x_878_, 8);
lean_inc_ref(v_moreLinkArgs_888_);
v_weakLinkArgs_889_ = lean_ctor_get(v_x_878_, 9);
lean_inc_ref(v_weakLinkArgs_889_);
v_backend_890_ = lean_ctor_get_uint8(v_x_878_, sizeof(void*)*13 + 1);
v_platformIndependent_891_ = lean_ctor_get(v_x_878_, 10);
lean_inc(v_platformIndependent_891_);
v_precompileImports_892_ = lean_ctor_get_uint8(v_x_878_, sizeof(void*)*13 + 2);
v_dynlibs_893_ = lean_ctor_get(v_x_878_, 11);
lean_inc_ref(v_dynlibs_893_);
v_plugins_894_ = lean_ctor_get(v_x_878_, 12);
lean_inc_ref(v_plugins_894_);
v_requiresModuleSystem_895_ = lean_ctor_get_uint8(v_x_878_, sizeof(void*)*13 + 3);
v_allowNonModules_896_ = lean_ctor_get_uint8(v_x_878_, sizeof(void*)*13 + 4);
lean_dec_ref(v_x_878_);
v___x_897_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_898_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_899_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = l_Lake_instReprBuildType_repr(v_buildType_879_, v___x_900_);
v___x_902_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = 0;
v___x_904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_898_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2));
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = lean_box(1);
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__9));
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_909_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_897_);
v___x_913_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__10, &l_Lake_instReprLeanConfig_repr___redArg___closed__10_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10);
v___x_914_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_880_);
v___x_915_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set_uint8(v___x_916_, sizeof(void*)*1, v___x_903_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_912_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_906_);
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___x_908_);
v___x_920_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__12));
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_897_);
v___x_923_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__13, &l_Lake_instReprLeanConfig_repr___redArg___closed__13_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13);
v___x_924_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_881_);
v___x_925_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*1, v___x_903_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_922_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_906_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_908_);
v___x_930_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__15));
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_897_);
v___x_933_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_882_);
v___x_934_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_923_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*1, v___x_903_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_932_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_906_);
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_908_);
v___x_939_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__17));
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_897_);
v___x_942_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__18, &l_Lake_instReprLeanConfig_repr___redArg___closed__18_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18);
v___x_943_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_883_);
v___x_944_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*1, v___x_903_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_941_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_906_);
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set(v___x_948_, 1, v___x_908_);
v___x_949_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__20));
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_897_);
v___x_952_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__21, &l_Lake_instReprLeanConfig_repr___redArg___closed__21_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21);
v___x_953_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_884_);
v___x_954_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set_uint8(v___x_955_, sizeof(void*)*1, v___x_903_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_951_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v___x_906_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_908_);
v___x_959_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__23));
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_897_);
v___x_962_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_885_);
v___x_963_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_942_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set_uint8(v___x_964_, sizeof(void*)*1, v___x_903_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_961_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_906_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_908_);
v___x_968_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__25));
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_967_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_897_);
v___x_971_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_886_);
v___x_972_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_923_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set_uint8(v___x_973_, sizeof(void*)*1, v___x_903_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_970_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_906_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_908_);
v___x_977_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__27));
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_897_);
v___x_980_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_887_);
v___x_981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_923_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_903_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_979_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_906_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_908_);
v___x_986_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__29));
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_897_);
v___x_989_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_888_);
v___x_990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_923_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_903_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_988_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_906_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_908_);
v___x_995_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__31));
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_897_);
v___x_998_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_889_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_923_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*1, v___x_903_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_997_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_906_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_908_);
v___x_1004_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__33));
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_897_);
v___x_1007_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__34, &l_Lake_instReprLeanConfig_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34);
v___x_1008_ = l_Lake_instReprBackend_repr(v_backend_890_, v___x_900_);
v___x_1009_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set_uint8(v___x_1010_, sizeof(void*)*1, v___x_903_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1006_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_906_);
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v___x_908_);
v___x_1014_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__36));
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_897_);
v___x_1017_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__37, &l_Lake_instReprLeanConfig_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37);
v___x_1018_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_891_, v___x_900_);
lean_dec(v_platformIndependent_891_);
v___x_1019_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set_uint8(v___x_1020_, sizeof(void*)*1, v___x_903_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1016_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set(v___x_1022_, 1, v___x_906_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_908_);
v___x_1024_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__39));
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1023_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set(v___x_1026_, 1, v___x_897_);
v___x_1027_ = l_Bool_repr___redArg(v_precompileImports_892_);
v___x_1028_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_952_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set_uint8(v___x_1029_, sizeof(void*)*1, v___x_903_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1026_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_906_);
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_908_);
v___x_1033_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__41));
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_897_);
v___x_1036_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_893_);
v___x_1037_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1007_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*1, v___x_903_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1035_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_906_);
v___x_1041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v___x_908_);
v___x_1042_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__43));
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1041_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_897_);
v___x_1045_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_894_);
v___x_1046_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1007_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*1, v___x_903_);
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1044_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_906_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_908_);
v___x_1051_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__45));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_897_);
v___x_1054_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__46, &l_Lake_instReprLeanConfig_repr___redArg___closed__46_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46);
v___x_1055_ = l_Bool_repr___redArg(v_requiresModuleSystem_895_);
v___x_1056_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set_uint8(v___x_1057_, sizeof(void*)*1, v___x_903_);
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1053_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_906_);
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_908_);
v___x_1061_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__48));
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___x_897_);
v___x_1064_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__49, &l_Lake_instReprLeanConfig_repr___redArg___closed__49_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49);
v___x_1065_ = l_Bool_repr___redArg(v_allowNonModules_896_);
v___x_1066_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set_uint8(v___x_1067_, sizeof(void*)*1, v___x_903_);
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1063_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__52, &l_Lake_instReprLeanConfig_repr___redArg___closed__52_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52);
v___x_1070_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__53));
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_1068_);
v___x_1072_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__54));
v___x_1073_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1069_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*1, v___x_903_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1076_, lean_object* v_prec_1077_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1079_, lean_object* v_prec_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lake_instReprLeanConfig_repr(v_x_1079_, v_prec_1080_);
lean_dec(v_prec_1080_);
return v_res_1081_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1084_){
_start:
{
uint8_t v_buildType_1085_; 
v_buildType_1085_ = lean_ctor_get_uint8(v_cfg_1084_, sizeof(void*)*13);
return v_buildType_1085_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1086_){
_start:
{
uint8_t v_res_1087_; lean_object* v_r_1088_; 
v_res_1087_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1086_);
lean_dec_ref(v_cfg_1086_);
v_r_1088_ = lean_box(v_res_1087_);
return v_r_1088_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1089_, lean_object* v_cfg_1090_){
_start:
{
lean_object* v_leanOptions_1091_; lean_object* v_moreLeanArgs_1092_; lean_object* v_weakLeanArgs_1093_; lean_object* v_moreLeancArgs_1094_; lean_object* v_moreServerOptions_1095_; lean_object* v_weakLeancArgs_1096_; lean_object* v_moreLinkObjs_1097_; lean_object* v_moreLinkLibs_1098_; lean_object* v_moreLinkArgs_1099_; lean_object* v_weakLinkArgs_1100_; uint8_t v_backend_1101_; lean_object* v_platformIndependent_1102_; uint8_t v_precompileImports_1103_; lean_object* v_dynlibs_1104_; lean_object* v_plugins_1105_; uint8_t v_requiresModuleSystem_1106_; uint8_t v_allowNonModules_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_leanOptions_1091_ = lean_ctor_get(v_cfg_1090_, 0);
v_moreLeanArgs_1092_ = lean_ctor_get(v_cfg_1090_, 1);
v_weakLeanArgs_1093_ = lean_ctor_get(v_cfg_1090_, 2);
v_moreLeancArgs_1094_ = lean_ctor_get(v_cfg_1090_, 3);
v_moreServerOptions_1095_ = lean_ctor_get(v_cfg_1090_, 4);
v_weakLeancArgs_1096_ = lean_ctor_get(v_cfg_1090_, 5);
v_moreLinkObjs_1097_ = lean_ctor_get(v_cfg_1090_, 6);
v_moreLinkLibs_1098_ = lean_ctor_get(v_cfg_1090_, 7);
v_moreLinkArgs_1099_ = lean_ctor_get(v_cfg_1090_, 8);
v_weakLinkArgs_1100_ = lean_ctor_get(v_cfg_1090_, 9);
v_backend_1101_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*13 + 1);
v_platformIndependent_1102_ = lean_ctor_get(v_cfg_1090_, 10);
v_precompileImports_1103_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*13 + 2);
v_dynlibs_1104_ = lean_ctor_get(v_cfg_1090_, 11);
v_plugins_1105_ = lean_ctor_get(v_cfg_1090_, 12);
v_requiresModuleSystem_1106_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*13 + 3);
v_allowNonModules_1107_ = lean_ctor_get_uint8(v_cfg_1090_, sizeof(void*)*13 + 4);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_cfg_1090_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v_cfg_1090_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_plugins_1105_);
lean_inc(v_dynlibs_1104_);
lean_inc(v_platformIndependent_1102_);
lean_inc(v_weakLinkArgs_1100_);
lean_inc(v_moreLinkArgs_1099_);
lean_inc(v_moreLinkLibs_1098_);
lean_inc(v_moreLinkObjs_1097_);
lean_inc(v_weakLeancArgs_1096_);
lean_inc(v_moreServerOptions_1095_);
lean_inc(v_moreLeancArgs_1094_);
lean_inc(v_weakLeanArgs_1093_);
lean_inc(v_moreLeanArgs_1092_);
lean_inc(v_leanOptions_1091_);
lean_dec(v_cfg_1090_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_leanOptions_1091_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_moreLeanArgs_1092_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_weakLeanArgs_1093_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_moreLeancArgs_1094_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_moreServerOptions_1095_);
lean_ctor_set(v_reuseFailAlloc_1113_, 5, v_weakLeancArgs_1096_);
lean_ctor_set(v_reuseFailAlloc_1113_, 6, v_moreLinkObjs_1097_);
lean_ctor_set(v_reuseFailAlloc_1113_, 7, v_moreLinkLibs_1098_);
lean_ctor_set(v_reuseFailAlloc_1113_, 8, v_moreLinkArgs_1099_);
lean_ctor_set(v_reuseFailAlloc_1113_, 9, v_weakLinkArgs_1100_);
lean_ctor_set(v_reuseFailAlloc_1113_, 10, v_platformIndependent_1102_);
lean_ctor_set(v_reuseFailAlloc_1113_, 11, v_dynlibs_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 12, v_plugins_1105_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*13 + 1, v_backend_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*13 + 2, v_precompileImports_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1106_);
lean_ctor_set_uint8(v_reuseFailAlloc_1113_, sizeof(void*)*13 + 4, v_allowNonModules_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_ctor_set_uint8(v___x_1112_, sizeof(void*)*13, v_val_1089_);
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1115_, lean_object* v_cfg_1116_){
_start:
{
uint8_t v_val_88__boxed_1117_; lean_object* v_res_1118_; 
v_val_88__boxed_1117_ = lean_unbox(v_val_1115_);
v_res_1118_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_88__boxed_1117_, v_cfg_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1119_, lean_object* v_cfg_1120_){
_start:
{
uint8_t v_buildType_1121_; lean_object* v_leanOptions_1122_; lean_object* v_moreLeanArgs_1123_; lean_object* v_weakLeanArgs_1124_; lean_object* v_moreLeancArgs_1125_; lean_object* v_moreServerOptions_1126_; lean_object* v_weakLeancArgs_1127_; lean_object* v_moreLinkObjs_1128_; lean_object* v_moreLinkLibs_1129_; lean_object* v_moreLinkArgs_1130_; lean_object* v_weakLinkArgs_1131_; uint8_t v_backend_1132_; lean_object* v_platformIndependent_1133_; uint8_t v_precompileImports_1134_; lean_object* v_dynlibs_1135_; lean_object* v_plugins_1136_; uint8_t v_requiresModuleSystem_1137_; uint8_t v_allowNonModules_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1148_; 
v_buildType_1121_ = lean_ctor_get_uint8(v_cfg_1120_, sizeof(void*)*13);
v_leanOptions_1122_ = lean_ctor_get(v_cfg_1120_, 0);
v_moreLeanArgs_1123_ = lean_ctor_get(v_cfg_1120_, 1);
v_weakLeanArgs_1124_ = lean_ctor_get(v_cfg_1120_, 2);
v_moreLeancArgs_1125_ = lean_ctor_get(v_cfg_1120_, 3);
v_moreServerOptions_1126_ = lean_ctor_get(v_cfg_1120_, 4);
v_weakLeancArgs_1127_ = lean_ctor_get(v_cfg_1120_, 5);
v_moreLinkObjs_1128_ = lean_ctor_get(v_cfg_1120_, 6);
v_moreLinkLibs_1129_ = lean_ctor_get(v_cfg_1120_, 7);
v_moreLinkArgs_1130_ = lean_ctor_get(v_cfg_1120_, 8);
v_weakLinkArgs_1131_ = lean_ctor_get(v_cfg_1120_, 9);
v_backend_1132_ = lean_ctor_get_uint8(v_cfg_1120_, sizeof(void*)*13 + 1);
v_platformIndependent_1133_ = lean_ctor_get(v_cfg_1120_, 10);
v_precompileImports_1134_ = lean_ctor_get_uint8(v_cfg_1120_, sizeof(void*)*13 + 2);
v_dynlibs_1135_ = lean_ctor_get(v_cfg_1120_, 11);
v_plugins_1136_ = lean_ctor_get(v_cfg_1120_, 12);
v_requiresModuleSystem_1137_ = lean_ctor_get_uint8(v_cfg_1120_, sizeof(void*)*13 + 3);
v_allowNonModules_1138_ = lean_ctor_get_uint8(v_cfg_1120_, sizeof(void*)*13 + 4);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_cfg_1120_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1140_ = v_cfg_1120_;
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_plugins_1136_);
lean_inc(v_dynlibs_1135_);
lean_inc(v_platformIndependent_1133_);
lean_inc(v_weakLinkArgs_1131_);
lean_inc(v_moreLinkArgs_1130_);
lean_inc(v_moreLinkLibs_1129_);
lean_inc(v_moreLinkObjs_1128_);
lean_inc(v_weakLeancArgs_1127_);
lean_inc(v_moreServerOptions_1126_);
lean_inc(v_moreLeancArgs_1125_);
lean_inc(v_weakLeanArgs_1124_);
lean_inc(v_moreLeanArgs_1123_);
lean_inc(v_leanOptions_1122_);
lean_dec(v_cfg_1120_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1148_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1142_ = lean_box(v_buildType_1121_);
v___x_1143_ = lean_apply_1(v_f_1119_, v___x_1142_);
if (v_isShared_1141_ == 0)
{
v___x_1145_ = v___x_1140_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_leanOptions_1122_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_moreLeanArgs_1123_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_weakLeanArgs_1124_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v_moreLeancArgs_1125_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_moreServerOptions_1126_);
lean_ctor_set(v_reuseFailAlloc_1147_, 5, v_weakLeancArgs_1127_);
lean_ctor_set(v_reuseFailAlloc_1147_, 6, v_moreLinkObjs_1128_);
lean_ctor_set(v_reuseFailAlloc_1147_, 7, v_moreLinkLibs_1129_);
lean_ctor_set(v_reuseFailAlloc_1147_, 8, v_moreLinkArgs_1130_);
lean_ctor_set(v_reuseFailAlloc_1147_, 9, v_weakLinkArgs_1131_);
lean_ctor_set(v_reuseFailAlloc_1147_, 10, v_platformIndependent_1133_);
lean_ctor_set(v_reuseFailAlloc_1147_, 11, v_dynlibs_1135_);
lean_ctor_set(v_reuseFailAlloc_1147_, 12, v_plugins_1136_);
v___x_1145_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_unbox(v___x_1143_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*13, v___x_1146_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*13 + 1, v_backend_1132_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*13 + 2, v_precompileImports_1134_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1137_);
lean_ctor_set_uint8(v___x_1145_, sizeof(void*)*13 + 4, v_allowNonModules_1138_);
return v___x_1145_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = 3;
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1151_);
lean_dec_ref(v_x_1151_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1165_){
_start:
{
lean_object* v_leanOptions_1166_; 
v_leanOptions_1166_ = lean_ctor_get(v_cfg_1165_, 0);
lean_inc_ref(v_leanOptions_1166_);
return v_leanOptions_1166_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1167_);
lean_dec_ref(v_cfg_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1169_, lean_object* v_cfg_1170_){
_start:
{
uint8_t v_buildType_1171_; lean_object* v_moreLeanArgs_1172_; lean_object* v_weakLeanArgs_1173_; lean_object* v_moreLeancArgs_1174_; lean_object* v_moreServerOptions_1175_; lean_object* v_weakLeancArgs_1176_; lean_object* v_moreLinkObjs_1177_; lean_object* v_moreLinkLibs_1178_; lean_object* v_moreLinkArgs_1179_; lean_object* v_weakLinkArgs_1180_; uint8_t v_backend_1181_; lean_object* v_platformIndependent_1182_; uint8_t v_precompileImports_1183_; lean_object* v_dynlibs_1184_; lean_object* v_plugins_1185_; uint8_t v_requiresModuleSystem_1186_; uint8_t v_allowNonModules_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
v_buildType_1171_ = lean_ctor_get_uint8(v_cfg_1170_, sizeof(void*)*13);
v_moreLeanArgs_1172_ = lean_ctor_get(v_cfg_1170_, 1);
v_weakLeanArgs_1173_ = lean_ctor_get(v_cfg_1170_, 2);
v_moreLeancArgs_1174_ = lean_ctor_get(v_cfg_1170_, 3);
v_moreServerOptions_1175_ = lean_ctor_get(v_cfg_1170_, 4);
v_weakLeancArgs_1176_ = lean_ctor_get(v_cfg_1170_, 5);
v_moreLinkObjs_1177_ = lean_ctor_get(v_cfg_1170_, 6);
v_moreLinkLibs_1178_ = lean_ctor_get(v_cfg_1170_, 7);
v_moreLinkArgs_1179_ = lean_ctor_get(v_cfg_1170_, 8);
v_weakLinkArgs_1180_ = lean_ctor_get(v_cfg_1170_, 9);
v_backend_1181_ = lean_ctor_get_uint8(v_cfg_1170_, sizeof(void*)*13 + 1);
v_platformIndependent_1182_ = lean_ctor_get(v_cfg_1170_, 10);
v_precompileImports_1183_ = lean_ctor_get_uint8(v_cfg_1170_, sizeof(void*)*13 + 2);
v_dynlibs_1184_ = lean_ctor_get(v_cfg_1170_, 11);
v_plugins_1185_ = lean_ctor_get(v_cfg_1170_, 12);
v_requiresModuleSystem_1186_ = lean_ctor_get_uint8(v_cfg_1170_, sizeof(void*)*13 + 3);
v_allowNonModules_1187_ = lean_ctor_get_uint8(v_cfg_1170_, sizeof(void*)*13 + 4);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_cfg_1170_);
if (v_isSharedCheck_1194_ == 0)
{
lean_object* v_unused_1195_; 
v_unused_1195_ = lean_ctor_get(v_cfg_1170_, 0);
lean_dec(v_unused_1195_);
v___x_1189_ = v_cfg_1170_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_plugins_1185_);
lean_inc(v_dynlibs_1184_);
lean_inc(v_platformIndependent_1182_);
lean_inc(v_weakLinkArgs_1180_);
lean_inc(v_moreLinkArgs_1179_);
lean_inc(v_moreLinkLibs_1178_);
lean_inc(v_moreLinkObjs_1177_);
lean_inc(v_weakLeancArgs_1176_);
lean_inc(v_moreServerOptions_1175_);
lean_inc(v_moreLeancArgs_1174_);
lean_inc(v_weakLeanArgs_1173_);
lean_inc(v_moreLeanArgs_1172_);
lean_dec(v_cfg_1170_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v_val_1169_);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_val_1169_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_moreLeanArgs_1172_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_weakLeanArgs_1173_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_moreLeancArgs_1174_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_moreServerOptions_1175_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_weakLeancArgs_1176_);
lean_ctor_set(v_reuseFailAlloc_1193_, 6, v_moreLinkObjs_1177_);
lean_ctor_set(v_reuseFailAlloc_1193_, 7, v_moreLinkLibs_1178_);
lean_ctor_set(v_reuseFailAlloc_1193_, 8, v_moreLinkArgs_1179_);
lean_ctor_set(v_reuseFailAlloc_1193_, 9, v_weakLinkArgs_1180_);
lean_ctor_set(v_reuseFailAlloc_1193_, 10, v_platformIndependent_1182_);
lean_ctor_set(v_reuseFailAlloc_1193_, 11, v_dynlibs_1184_);
lean_ctor_set(v_reuseFailAlloc_1193_, 12, v_plugins_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*13, v_buildType_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*13 + 1, v_backend_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*13 + 2, v_precompileImports_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1193_, sizeof(void*)*13 + 4, v_allowNonModules_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1196_, lean_object* v_cfg_1197_){
_start:
{
uint8_t v_buildType_1198_; lean_object* v_leanOptions_1199_; lean_object* v_moreLeanArgs_1200_; lean_object* v_weakLeanArgs_1201_; lean_object* v_moreLeancArgs_1202_; lean_object* v_moreServerOptions_1203_; lean_object* v_weakLeancArgs_1204_; lean_object* v_moreLinkObjs_1205_; lean_object* v_moreLinkLibs_1206_; lean_object* v_moreLinkArgs_1207_; lean_object* v_weakLinkArgs_1208_; uint8_t v_backend_1209_; lean_object* v_platformIndependent_1210_; uint8_t v_precompileImports_1211_; lean_object* v_dynlibs_1212_; lean_object* v_plugins_1213_; uint8_t v_requiresModuleSystem_1214_; uint8_t v_allowNonModules_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_buildType_1198_ = lean_ctor_get_uint8(v_cfg_1197_, sizeof(void*)*13);
v_leanOptions_1199_ = lean_ctor_get(v_cfg_1197_, 0);
v_moreLeanArgs_1200_ = lean_ctor_get(v_cfg_1197_, 1);
v_weakLeanArgs_1201_ = lean_ctor_get(v_cfg_1197_, 2);
v_moreLeancArgs_1202_ = lean_ctor_get(v_cfg_1197_, 3);
v_moreServerOptions_1203_ = lean_ctor_get(v_cfg_1197_, 4);
v_weakLeancArgs_1204_ = lean_ctor_get(v_cfg_1197_, 5);
v_moreLinkObjs_1205_ = lean_ctor_get(v_cfg_1197_, 6);
v_moreLinkLibs_1206_ = lean_ctor_get(v_cfg_1197_, 7);
v_moreLinkArgs_1207_ = lean_ctor_get(v_cfg_1197_, 8);
v_weakLinkArgs_1208_ = lean_ctor_get(v_cfg_1197_, 9);
v_backend_1209_ = lean_ctor_get_uint8(v_cfg_1197_, sizeof(void*)*13 + 1);
v_platformIndependent_1210_ = lean_ctor_get(v_cfg_1197_, 10);
v_precompileImports_1211_ = lean_ctor_get_uint8(v_cfg_1197_, sizeof(void*)*13 + 2);
v_dynlibs_1212_ = lean_ctor_get(v_cfg_1197_, 11);
v_plugins_1213_ = lean_ctor_get(v_cfg_1197_, 12);
v_requiresModuleSystem_1214_ = lean_ctor_get_uint8(v_cfg_1197_, sizeof(void*)*13 + 3);
v_allowNonModules_1215_ = lean_ctor_get_uint8(v_cfg_1197_, sizeof(void*)*13 + 4);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_cfg_1197_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v_cfg_1197_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_plugins_1213_);
lean_inc(v_dynlibs_1212_);
lean_inc(v_platformIndependent_1210_);
lean_inc(v_weakLinkArgs_1208_);
lean_inc(v_moreLinkArgs_1207_);
lean_inc(v_moreLinkLibs_1206_);
lean_inc(v_moreLinkObjs_1205_);
lean_inc(v_weakLeancArgs_1204_);
lean_inc(v_moreServerOptions_1203_);
lean_inc(v_moreLeancArgs_1202_);
lean_inc(v_weakLeanArgs_1201_);
lean_inc(v_moreLeanArgs_1200_);
lean_inc(v_leanOptions_1199_);
lean_dec(v_cfg_1197_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1221_; 
v___x_1219_ = lean_apply_1(v_f_1196_, v_leanOptions_1199_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_moreLeanArgs_1200_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_weakLeanArgs_1201_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_moreLeancArgs_1202_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_moreServerOptions_1203_);
lean_ctor_set(v_reuseFailAlloc_1222_, 5, v_weakLeancArgs_1204_);
lean_ctor_set(v_reuseFailAlloc_1222_, 6, v_moreLinkObjs_1205_);
lean_ctor_set(v_reuseFailAlloc_1222_, 7, v_moreLinkLibs_1206_);
lean_ctor_set(v_reuseFailAlloc_1222_, 8, v_moreLinkArgs_1207_);
lean_ctor_set(v_reuseFailAlloc_1222_, 9, v_weakLinkArgs_1208_);
lean_ctor_set(v_reuseFailAlloc_1222_, 10, v_platformIndependent_1210_);
lean_ctor_set(v_reuseFailAlloc_1222_, 11, v_dynlibs_1212_);
lean_ctor_set(v_reuseFailAlloc_1222_, 12, v_plugins_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*13, v_buildType_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*13 + 1, v_backend_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*13 + 2, v_precompileImports_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1214_);
lean_ctor_set_uint8(v_reuseFailAlloc_1222_, sizeof(void*)*13 + 4, v_allowNonModules_1215_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1226_);
lean_dec_ref(v_x_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1239_){
_start:
{
lean_object* v_moreLeanArgs_1240_; 
v_moreLeanArgs_1240_ = lean_ctor_get(v_cfg_1239_, 1);
lean_inc_ref(v_moreLeanArgs_1240_);
return v_moreLeanArgs_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1241_);
lean_dec_ref(v_cfg_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1243_, lean_object* v_cfg_1244_){
_start:
{
uint8_t v_buildType_1245_; lean_object* v_leanOptions_1246_; lean_object* v_weakLeanArgs_1247_; lean_object* v_moreLeancArgs_1248_; lean_object* v_moreServerOptions_1249_; lean_object* v_weakLeancArgs_1250_; lean_object* v_moreLinkObjs_1251_; lean_object* v_moreLinkLibs_1252_; lean_object* v_moreLinkArgs_1253_; lean_object* v_weakLinkArgs_1254_; uint8_t v_backend_1255_; lean_object* v_platformIndependent_1256_; uint8_t v_precompileImports_1257_; lean_object* v_dynlibs_1258_; lean_object* v_plugins_1259_; uint8_t v_requiresModuleSystem_1260_; uint8_t v_allowNonModules_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_buildType_1245_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*13);
v_leanOptions_1246_ = lean_ctor_get(v_cfg_1244_, 0);
v_weakLeanArgs_1247_ = lean_ctor_get(v_cfg_1244_, 2);
v_moreLeancArgs_1248_ = lean_ctor_get(v_cfg_1244_, 3);
v_moreServerOptions_1249_ = lean_ctor_get(v_cfg_1244_, 4);
v_weakLeancArgs_1250_ = lean_ctor_get(v_cfg_1244_, 5);
v_moreLinkObjs_1251_ = lean_ctor_get(v_cfg_1244_, 6);
v_moreLinkLibs_1252_ = lean_ctor_get(v_cfg_1244_, 7);
v_moreLinkArgs_1253_ = lean_ctor_get(v_cfg_1244_, 8);
v_weakLinkArgs_1254_ = lean_ctor_get(v_cfg_1244_, 9);
v_backend_1255_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*13 + 1);
v_platformIndependent_1256_ = lean_ctor_get(v_cfg_1244_, 10);
v_precompileImports_1257_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*13 + 2);
v_dynlibs_1258_ = lean_ctor_get(v_cfg_1244_, 11);
v_plugins_1259_ = lean_ctor_get(v_cfg_1244_, 12);
v_requiresModuleSystem_1260_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*13 + 3);
v_allowNonModules_1261_ = lean_ctor_get_uint8(v_cfg_1244_, sizeof(void*)*13 + 4);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_cfg_1244_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v_cfg_1244_, 1);
lean_dec(v_unused_1269_);
v___x_1263_ = v_cfg_1244_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_plugins_1259_);
lean_inc(v_dynlibs_1258_);
lean_inc(v_platformIndependent_1256_);
lean_inc(v_weakLinkArgs_1254_);
lean_inc(v_moreLinkArgs_1253_);
lean_inc(v_moreLinkLibs_1252_);
lean_inc(v_moreLinkObjs_1251_);
lean_inc(v_weakLeancArgs_1250_);
lean_inc(v_moreServerOptions_1249_);
lean_inc(v_moreLeancArgs_1248_);
lean_inc(v_weakLeanArgs_1247_);
lean_inc(v_leanOptions_1246_);
lean_dec(v_cfg_1244_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_val_1243_);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_leanOptions_1246_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_val_1243_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_weakLeanArgs_1247_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_moreLeancArgs_1248_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_moreServerOptions_1249_);
lean_ctor_set(v_reuseFailAlloc_1267_, 5, v_weakLeancArgs_1250_);
lean_ctor_set(v_reuseFailAlloc_1267_, 6, v_moreLinkObjs_1251_);
lean_ctor_set(v_reuseFailAlloc_1267_, 7, v_moreLinkLibs_1252_);
lean_ctor_set(v_reuseFailAlloc_1267_, 8, v_moreLinkArgs_1253_);
lean_ctor_set(v_reuseFailAlloc_1267_, 9, v_weakLinkArgs_1254_);
lean_ctor_set(v_reuseFailAlloc_1267_, 10, v_platformIndependent_1256_);
lean_ctor_set(v_reuseFailAlloc_1267_, 11, v_dynlibs_1258_);
lean_ctor_set(v_reuseFailAlloc_1267_, 12, v_plugins_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*13, v_buildType_1245_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*13 + 1, v_backend_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*13 + 2, v_precompileImports_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1267_, sizeof(void*)*13 + 4, v_allowNonModules_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1270_, lean_object* v_cfg_1271_){
_start:
{
uint8_t v_buildType_1272_; lean_object* v_leanOptions_1273_; lean_object* v_moreLeanArgs_1274_; lean_object* v_weakLeanArgs_1275_; lean_object* v_moreLeancArgs_1276_; lean_object* v_moreServerOptions_1277_; lean_object* v_weakLeancArgs_1278_; lean_object* v_moreLinkObjs_1279_; lean_object* v_moreLinkLibs_1280_; lean_object* v_moreLinkArgs_1281_; lean_object* v_weakLinkArgs_1282_; uint8_t v_backend_1283_; lean_object* v_platformIndependent_1284_; uint8_t v_precompileImports_1285_; lean_object* v_dynlibs_1286_; lean_object* v_plugins_1287_; uint8_t v_requiresModuleSystem_1288_; uint8_t v_allowNonModules_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1297_; 
v_buildType_1272_ = lean_ctor_get_uint8(v_cfg_1271_, sizeof(void*)*13);
v_leanOptions_1273_ = lean_ctor_get(v_cfg_1271_, 0);
v_moreLeanArgs_1274_ = lean_ctor_get(v_cfg_1271_, 1);
v_weakLeanArgs_1275_ = lean_ctor_get(v_cfg_1271_, 2);
v_moreLeancArgs_1276_ = lean_ctor_get(v_cfg_1271_, 3);
v_moreServerOptions_1277_ = lean_ctor_get(v_cfg_1271_, 4);
v_weakLeancArgs_1278_ = lean_ctor_get(v_cfg_1271_, 5);
v_moreLinkObjs_1279_ = lean_ctor_get(v_cfg_1271_, 6);
v_moreLinkLibs_1280_ = lean_ctor_get(v_cfg_1271_, 7);
v_moreLinkArgs_1281_ = lean_ctor_get(v_cfg_1271_, 8);
v_weakLinkArgs_1282_ = lean_ctor_get(v_cfg_1271_, 9);
v_backend_1283_ = lean_ctor_get_uint8(v_cfg_1271_, sizeof(void*)*13 + 1);
v_platformIndependent_1284_ = lean_ctor_get(v_cfg_1271_, 10);
v_precompileImports_1285_ = lean_ctor_get_uint8(v_cfg_1271_, sizeof(void*)*13 + 2);
v_dynlibs_1286_ = lean_ctor_get(v_cfg_1271_, 11);
v_plugins_1287_ = lean_ctor_get(v_cfg_1271_, 12);
v_requiresModuleSystem_1288_ = lean_ctor_get_uint8(v_cfg_1271_, sizeof(void*)*13 + 3);
v_allowNonModules_1289_ = lean_ctor_get_uint8(v_cfg_1271_, sizeof(void*)*13 + 4);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_cfg_1271_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1291_ = v_cfg_1271_;
v_isShared_1292_ = v_isSharedCheck_1297_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_plugins_1287_);
lean_inc(v_dynlibs_1286_);
lean_inc(v_platformIndependent_1284_);
lean_inc(v_weakLinkArgs_1282_);
lean_inc(v_moreLinkArgs_1281_);
lean_inc(v_moreLinkLibs_1280_);
lean_inc(v_moreLinkObjs_1279_);
lean_inc(v_weakLeancArgs_1278_);
lean_inc(v_moreServerOptions_1277_);
lean_inc(v_moreLeancArgs_1276_);
lean_inc(v_weakLeanArgs_1275_);
lean_inc(v_moreLeanArgs_1274_);
lean_inc(v_leanOptions_1273_);
lean_dec(v_cfg_1271_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1297_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1293_ = lean_apply_1(v_f_1270_, v_moreLeanArgs_1274_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 1, v___x_1293_);
v___x_1295_ = v___x_1291_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_leanOptions_1273_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_weakLeanArgs_1275_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_moreLeancArgs_1276_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_moreServerOptions_1277_);
lean_ctor_set(v_reuseFailAlloc_1296_, 5, v_weakLeancArgs_1278_);
lean_ctor_set(v_reuseFailAlloc_1296_, 6, v_moreLinkObjs_1279_);
lean_ctor_set(v_reuseFailAlloc_1296_, 7, v_moreLinkLibs_1280_);
lean_ctor_set(v_reuseFailAlloc_1296_, 8, v_moreLinkArgs_1281_);
lean_ctor_set(v_reuseFailAlloc_1296_, 9, v_weakLinkArgs_1282_);
lean_ctor_set(v_reuseFailAlloc_1296_, 10, v_platformIndependent_1284_);
lean_ctor_set(v_reuseFailAlloc_1296_, 11, v_dynlibs_1286_);
lean_ctor_set(v_reuseFailAlloc_1296_, 12, v_plugins_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*13, v_buildType_1272_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*13 + 1, v_backend_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*13 + 2, v_precompileImports_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1288_);
lean_ctor_set_uint8(v_reuseFailAlloc_1296_, sizeof(void*)*13 + 4, v_allowNonModules_1289_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = ((lean_object*)(l_Lake_BuildType_leanArgs___redArg___closed__0));
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1300_);
lean_dec_ref(v_x_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1313_){
_start:
{
lean_object* v_weakLeanArgs_1314_; 
v_weakLeanArgs_1314_ = lean_ctor_get(v_cfg_1313_, 2);
lean_inc_ref(v_weakLeanArgs_1314_);
return v_weakLeanArgs_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1315_);
lean_dec_ref(v_cfg_1315_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1317_, lean_object* v_cfg_1318_){
_start:
{
uint8_t v_buildType_1319_; lean_object* v_leanOptions_1320_; lean_object* v_moreLeanArgs_1321_; lean_object* v_moreLeancArgs_1322_; lean_object* v_moreServerOptions_1323_; lean_object* v_weakLeancArgs_1324_; lean_object* v_moreLinkObjs_1325_; lean_object* v_moreLinkLibs_1326_; lean_object* v_moreLinkArgs_1327_; lean_object* v_weakLinkArgs_1328_; uint8_t v_backend_1329_; lean_object* v_platformIndependent_1330_; uint8_t v_precompileImports_1331_; lean_object* v_dynlibs_1332_; lean_object* v_plugins_1333_; uint8_t v_requiresModuleSystem_1334_; uint8_t v_allowNonModules_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_buildType_1319_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13);
v_leanOptions_1320_ = lean_ctor_get(v_cfg_1318_, 0);
v_moreLeanArgs_1321_ = lean_ctor_get(v_cfg_1318_, 1);
v_moreLeancArgs_1322_ = lean_ctor_get(v_cfg_1318_, 3);
v_moreServerOptions_1323_ = lean_ctor_get(v_cfg_1318_, 4);
v_weakLeancArgs_1324_ = lean_ctor_get(v_cfg_1318_, 5);
v_moreLinkObjs_1325_ = lean_ctor_get(v_cfg_1318_, 6);
v_moreLinkLibs_1326_ = lean_ctor_get(v_cfg_1318_, 7);
v_moreLinkArgs_1327_ = lean_ctor_get(v_cfg_1318_, 8);
v_weakLinkArgs_1328_ = lean_ctor_get(v_cfg_1318_, 9);
v_backend_1329_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13 + 1);
v_platformIndependent_1330_ = lean_ctor_get(v_cfg_1318_, 10);
v_precompileImports_1331_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13 + 2);
v_dynlibs_1332_ = lean_ctor_get(v_cfg_1318_, 11);
v_plugins_1333_ = lean_ctor_get(v_cfg_1318_, 12);
v_requiresModuleSystem_1334_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13 + 3);
v_allowNonModules_1335_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13 + 4);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_cfg_1318_);
if (v_isSharedCheck_1342_ == 0)
{
lean_object* v_unused_1343_; 
v_unused_1343_ = lean_ctor_get(v_cfg_1318_, 2);
lean_dec(v_unused_1343_);
v___x_1337_ = v_cfg_1318_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_plugins_1333_);
lean_inc(v_dynlibs_1332_);
lean_inc(v_platformIndependent_1330_);
lean_inc(v_weakLinkArgs_1328_);
lean_inc(v_moreLinkArgs_1327_);
lean_inc(v_moreLinkLibs_1326_);
lean_inc(v_moreLinkObjs_1325_);
lean_inc(v_weakLeancArgs_1324_);
lean_inc(v_moreServerOptions_1323_);
lean_inc(v_moreLeancArgs_1322_);
lean_inc(v_moreLeanArgs_1321_);
lean_inc(v_leanOptions_1320_);
lean_dec(v_cfg_1318_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 2, v_val_1317_);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_leanOptions_1320_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_moreLeanArgs_1321_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_val_1317_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_moreLeancArgs_1322_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_moreServerOptions_1323_);
lean_ctor_set(v_reuseFailAlloc_1341_, 5, v_weakLeancArgs_1324_);
lean_ctor_set(v_reuseFailAlloc_1341_, 6, v_moreLinkObjs_1325_);
lean_ctor_set(v_reuseFailAlloc_1341_, 7, v_moreLinkLibs_1326_);
lean_ctor_set(v_reuseFailAlloc_1341_, 8, v_moreLinkArgs_1327_);
lean_ctor_set(v_reuseFailAlloc_1341_, 9, v_weakLinkArgs_1328_);
lean_ctor_set(v_reuseFailAlloc_1341_, 10, v_platformIndependent_1330_);
lean_ctor_set(v_reuseFailAlloc_1341_, 11, v_dynlibs_1332_);
lean_ctor_set(v_reuseFailAlloc_1341_, 12, v_plugins_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13, v_buildType_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13 + 1, v_backend_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13 + 2, v_precompileImports_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13 + 4, v_allowNonModules_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1344_, lean_object* v_cfg_1345_){
_start:
{
uint8_t v_buildType_1346_; lean_object* v_leanOptions_1347_; lean_object* v_moreLeanArgs_1348_; lean_object* v_weakLeanArgs_1349_; lean_object* v_moreLeancArgs_1350_; lean_object* v_moreServerOptions_1351_; lean_object* v_weakLeancArgs_1352_; lean_object* v_moreLinkObjs_1353_; lean_object* v_moreLinkLibs_1354_; lean_object* v_moreLinkArgs_1355_; lean_object* v_weakLinkArgs_1356_; uint8_t v_backend_1357_; lean_object* v_platformIndependent_1358_; uint8_t v_precompileImports_1359_; lean_object* v_dynlibs_1360_; lean_object* v_plugins_1361_; uint8_t v_requiresModuleSystem_1362_; uint8_t v_allowNonModules_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1371_; 
v_buildType_1346_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*13);
v_leanOptions_1347_ = lean_ctor_get(v_cfg_1345_, 0);
v_moreLeanArgs_1348_ = lean_ctor_get(v_cfg_1345_, 1);
v_weakLeanArgs_1349_ = lean_ctor_get(v_cfg_1345_, 2);
v_moreLeancArgs_1350_ = lean_ctor_get(v_cfg_1345_, 3);
v_moreServerOptions_1351_ = lean_ctor_get(v_cfg_1345_, 4);
v_weakLeancArgs_1352_ = lean_ctor_get(v_cfg_1345_, 5);
v_moreLinkObjs_1353_ = lean_ctor_get(v_cfg_1345_, 6);
v_moreLinkLibs_1354_ = lean_ctor_get(v_cfg_1345_, 7);
v_moreLinkArgs_1355_ = lean_ctor_get(v_cfg_1345_, 8);
v_weakLinkArgs_1356_ = lean_ctor_get(v_cfg_1345_, 9);
v_backend_1357_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*13 + 1);
v_platformIndependent_1358_ = lean_ctor_get(v_cfg_1345_, 10);
v_precompileImports_1359_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*13 + 2);
v_dynlibs_1360_ = lean_ctor_get(v_cfg_1345_, 11);
v_plugins_1361_ = lean_ctor_get(v_cfg_1345_, 12);
v_requiresModuleSystem_1362_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*13 + 3);
v_allowNonModules_1363_ = lean_ctor_get_uint8(v_cfg_1345_, sizeof(void*)*13 + 4);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_cfg_1345_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1365_ = v_cfg_1345_;
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_plugins_1361_);
lean_inc(v_dynlibs_1360_);
lean_inc(v_platformIndependent_1358_);
lean_inc(v_weakLinkArgs_1356_);
lean_inc(v_moreLinkArgs_1355_);
lean_inc(v_moreLinkLibs_1354_);
lean_inc(v_moreLinkObjs_1353_);
lean_inc(v_weakLeancArgs_1352_);
lean_inc(v_moreServerOptions_1351_);
lean_inc(v_moreLeancArgs_1350_);
lean_inc(v_weakLeanArgs_1349_);
lean_inc(v_moreLeanArgs_1348_);
lean_inc(v_leanOptions_1347_);
lean_dec(v_cfg_1345_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1371_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = lean_apply_1(v_f_1344_, v_weakLeanArgs_1349_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 2, v___x_1367_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_leanOptions_1347_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_moreLeanArgs_1348_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_moreLeancArgs_1350_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_moreServerOptions_1351_);
lean_ctor_set(v_reuseFailAlloc_1370_, 5, v_weakLeancArgs_1352_);
lean_ctor_set(v_reuseFailAlloc_1370_, 6, v_moreLinkObjs_1353_);
lean_ctor_set(v_reuseFailAlloc_1370_, 7, v_moreLinkLibs_1354_);
lean_ctor_set(v_reuseFailAlloc_1370_, 8, v_moreLinkArgs_1355_);
lean_ctor_set(v_reuseFailAlloc_1370_, 9, v_weakLinkArgs_1356_);
lean_ctor_set(v_reuseFailAlloc_1370_, 10, v_platformIndependent_1358_);
lean_ctor_set(v_reuseFailAlloc_1370_, 11, v_dynlibs_1360_);
lean_ctor_set(v_reuseFailAlloc_1370_, 12, v_plugins_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*13, v_buildType_1346_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*13 + 1, v_backend_1357_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*13 + 2, v_precompileImports_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1362_);
lean_ctor_set_uint8(v_reuseFailAlloc_1370_, sizeof(void*)*13 + 4, v_allowNonModules_1363_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1382_){
_start:
{
lean_object* v_moreLeancArgs_1383_; 
v_moreLeancArgs_1383_ = lean_ctor_get(v_cfg_1382_, 3);
lean_inc_ref(v_moreLeancArgs_1383_);
return v_moreLeancArgs_1383_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1384_);
lean_dec_ref(v_cfg_1384_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1386_, lean_object* v_cfg_1387_){
_start:
{
uint8_t v_buildType_1388_; lean_object* v_leanOptions_1389_; lean_object* v_moreLeanArgs_1390_; lean_object* v_weakLeanArgs_1391_; lean_object* v_moreServerOptions_1392_; lean_object* v_weakLeancArgs_1393_; lean_object* v_moreLinkObjs_1394_; lean_object* v_moreLinkLibs_1395_; lean_object* v_moreLinkArgs_1396_; lean_object* v_weakLinkArgs_1397_; uint8_t v_backend_1398_; lean_object* v_platformIndependent_1399_; uint8_t v_precompileImports_1400_; lean_object* v_dynlibs_1401_; lean_object* v_plugins_1402_; uint8_t v_requiresModuleSystem_1403_; uint8_t v_allowNonModules_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
v_buildType_1388_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*13);
v_leanOptions_1389_ = lean_ctor_get(v_cfg_1387_, 0);
v_moreLeanArgs_1390_ = lean_ctor_get(v_cfg_1387_, 1);
v_weakLeanArgs_1391_ = lean_ctor_get(v_cfg_1387_, 2);
v_moreServerOptions_1392_ = lean_ctor_get(v_cfg_1387_, 4);
v_weakLeancArgs_1393_ = lean_ctor_get(v_cfg_1387_, 5);
v_moreLinkObjs_1394_ = lean_ctor_get(v_cfg_1387_, 6);
v_moreLinkLibs_1395_ = lean_ctor_get(v_cfg_1387_, 7);
v_moreLinkArgs_1396_ = lean_ctor_get(v_cfg_1387_, 8);
v_weakLinkArgs_1397_ = lean_ctor_get(v_cfg_1387_, 9);
v_backend_1398_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*13 + 1);
v_platformIndependent_1399_ = lean_ctor_get(v_cfg_1387_, 10);
v_precompileImports_1400_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*13 + 2);
v_dynlibs_1401_ = lean_ctor_get(v_cfg_1387_, 11);
v_plugins_1402_ = lean_ctor_get(v_cfg_1387_, 12);
v_requiresModuleSystem_1403_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*13 + 3);
v_allowNonModules_1404_ = lean_ctor_get_uint8(v_cfg_1387_, sizeof(void*)*13 + 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_cfg_1387_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_cfg_1387_, 3);
lean_dec(v_unused_1412_);
v___x_1406_ = v_cfg_1387_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_plugins_1402_);
lean_inc(v_dynlibs_1401_);
lean_inc(v_platformIndependent_1399_);
lean_inc(v_weakLinkArgs_1397_);
lean_inc(v_moreLinkArgs_1396_);
lean_inc(v_moreLinkLibs_1395_);
lean_inc(v_moreLinkObjs_1394_);
lean_inc(v_weakLeancArgs_1393_);
lean_inc(v_moreServerOptions_1392_);
lean_inc(v_weakLeanArgs_1391_);
lean_inc(v_moreLeanArgs_1390_);
lean_inc(v_leanOptions_1389_);
lean_dec(v_cfg_1387_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 3, v_val_1386_);
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_leanOptions_1389_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_moreLeanArgs_1390_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_weakLeanArgs_1391_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_val_1386_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v_moreServerOptions_1392_);
lean_ctor_set(v_reuseFailAlloc_1410_, 5, v_weakLeancArgs_1393_);
lean_ctor_set(v_reuseFailAlloc_1410_, 6, v_moreLinkObjs_1394_);
lean_ctor_set(v_reuseFailAlloc_1410_, 7, v_moreLinkLibs_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 8, v_moreLinkArgs_1396_);
lean_ctor_set(v_reuseFailAlloc_1410_, 9, v_weakLinkArgs_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 10, v_platformIndependent_1399_);
lean_ctor_set(v_reuseFailAlloc_1410_, 11, v_dynlibs_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 12, v_plugins_1402_);
lean_ctor_set_uint8(v_reuseFailAlloc_1410_, sizeof(void*)*13, v_buildType_1388_);
lean_ctor_set_uint8(v_reuseFailAlloc_1410_, sizeof(void*)*13 + 1, v_backend_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1410_, sizeof(void*)*13 + 2, v_precompileImports_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1410_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1403_);
lean_ctor_set_uint8(v_reuseFailAlloc_1410_, sizeof(void*)*13 + 4, v_allowNonModules_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1413_, lean_object* v_cfg_1414_){
_start:
{
uint8_t v_buildType_1415_; lean_object* v_leanOptions_1416_; lean_object* v_moreLeanArgs_1417_; lean_object* v_weakLeanArgs_1418_; lean_object* v_moreLeancArgs_1419_; lean_object* v_moreServerOptions_1420_; lean_object* v_weakLeancArgs_1421_; lean_object* v_moreLinkObjs_1422_; lean_object* v_moreLinkLibs_1423_; lean_object* v_moreLinkArgs_1424_; lean_object* v_weakLinkArgs_1425_; uint8_t v_backend_1426_; lean_object* v_platformIndependent_1427_; uint8_t v_precompileImports_1428_; lean_object* v_dynlibs_1429_; lean_object* v_plugins_1430_; uint8_t v_requiresModuleSystem_1431_; uint8_t v_allowNonModules_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1440_; 
v_buildType_1415_ = lean_ctor_get_uint8(v_cfg_1414_, sizeof(void*)*13);
v_leanOptions_1416_ = lean_ctor_get(v_cfg_1414_, 0);
v_moreLeanArgs_1417_ = lean_ctor_get(v_cfg_1414_, 1);
v_weakLeanArgs_1418_ = lean_ctor_get(v_cfg_1414_, 2);
v_moreLeancArgs_1419_ = lean_ctor_get(v_cfg_1414_, 3);
v_moreServerOptions_1420_ = lean_ctor_get(v_cfg_1414_, 4);
v_weakLeancArgs_1421_ = lean_ctor_get(v_cfg_1414_, 5);
v_moreLinkObjs_1422_ = lean_ctor_get(v_cfg_1414_, 6);
v_moreLinkLibs_1423_ = lean_ctor_get(v_cfg_1414_, 7);
v_moreLinkArgs_1424_ = lean_ctor_get(v_cfg_1414_, 8);
v_weakLinkArgs_1425_ = lean_ctor_get(v_cfg_1414_, 9);
v_backend_1426_ = lean_ctor_get_uint8(v_cfg_1414_, sizeof(void*)*13 + 1);
v_platformIndependent_1427_ = lean_ctor_get(v_cfg_1414_, 10);
v_precompileImports_1428_ = lean_ctor_get_uint8(v_cfg_1414_, sizeof(void*)*13 + 2);
v_dynlibs_1429_ = lean_ctor_get(v_cfg_1414_, 11);
v_plugins_1430_ = lean_ctor_get(v_cfg_1414_, 12);
v_requiresModuleSystem_1431_ = lean_ctor_get_uint8(v_cfg_1414_, sizeof(void*)*13 + 3);
v_allowNonModules_1432_ = lean_ctor_get_uint8(v_cfg_1414_, sizeof(void*)*13 + 4);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_cfg_1414_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1434_ = v_cfg_1414_;
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_plugins_1430_);
lean_inc(v_dynlibs_1429_);
lean_inc(v_platformIndependent_1427_);
lean_inc(v_weakLinkArgs_1425_);
lean_inc(v_moreLinkArgs_1424_);
lean_inc(v_moreLinkLibs_1423_);
lean_inc(v_moreLinkObjs_1422_);
lean_inc(v_weakLeancArgs_1421_);
lean_inc(v_moreServerOptions_1420_);
lean_inc(v_moreLeancArgs_1419_);
lean_inc(v_weakLeanArgs_1418_);
lean_inc(v_moreLeanArgs_1417_);
lean_inc(v_leanOptions_1416_);
lean_dec(v_cfg_1414_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1440_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1438_; 
v___x_1436_ = lean_apply_1(v_f_1413_, v_moreLeancArgs_1419_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 3, v___x_1436_);
v___x_1438_ = v___x_1434_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_leanOptions_1416_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_moreLeanArgs_1417_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v_weakLeanArgs_1418_);
lean_ctor_set(v_reuseFailAlloc_1439_, 3, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1439_, 4, v_moreServerOptions_1420_);
lean_ctor_set(v_reuseFailAlloc_1439_, 5, v_weakLeancArgs_1421_);
lean_ctor_set(v_reuseFailAlloc_1439_, 6, v_moreLinkObjs_1422_);
lean_ctor_set(v_reuseFailAlloc_1439_, 7, v_moreLinkLibs_1423_);
lean_ctor_set(v_reuseFailAlloc_1439_, 8, v_moreLinkArgs_1424_);
lean_ctor_set(v_reuseFailAlloc_1439_, 9, v_weakLinkArgs_1425_);
lean_ctor_set(v_reuseFailAlloc_1439_, 10, v_platformIndependent_1427_);
lean_ctor_set(v_reuseFailAlloc_1439_, 11, v_dynlibs_1429_);
lean_ctor_set(v_reuseFailAlloc_1439_, 12, v_plugins_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1439_, sizeof(void*)*13, v_buildType_1415_);
lean_ctor_set_uint8(v_reuseFailAlloc_1439_, sizeof(void*)*13 + 1, v_backend_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1439_, sizeof(void*)*13 + 2, v_precompileImports_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1439_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1431_);
lean_ctor_set_uint8(v_reuseFailAlloc_1439_, sizeof(void*)*13 + 4, v_allowNonModules_1432_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1451_){
_start:
{
lean_object* v_moreServerOptions_1452_; 
v_moreServerOptions_1452_ = lean_ctor_get(v_cfg_1451_, 4);
lean_inc_ref(v_moreServerOptions_1452_);
return v_moreServerOptions_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1453_);
lean_dec_ref(v_cfg_1453_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1455_, lean_object* v_cfg_1456_){
_start:
{
uint8_t v_buildType_1457_; lean_object* v_leanOptions_1458_; lean_object* v_moreLeanArgs_1459_; lean_object* v_weakLeanArgs_1460_; lean_object* v_moreLeancArgs_1461_; lean_object* v_weakLeancArgs_1462_; lean_object* v_moreLinkObjs_1463_; lean_object* v_moreLinkLibs_1464_; lean_object* v_moreLinkArgs_1465_; lean_object* v_weakLinkArgs_1466_; uint8_t v_backend_1467_; lean_object* v_platformIndependent_1468_; uint8_t v_precompileImports_1469_; lean_object* v_dynlibs_1470_; lean_object* v_plugins_1471_; uint8_t v_requiresModuleSystem_1472_; uint8_t v_allowNonModules_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
v_buildType_1457_ = lean_ctor_get_uint8(v_cfg_1456_, sizeof(void*)*13);
v_leanOptions_1458_ = lean_ctor_get(v_cfg_1456_, 0);
v_moreLeanArgs_1459_ = lean_ctor_get(v_cfg_1456_, 1);
v_weakLeanArgs_1460_ = lean_ctor_get(v_cfg_1456_, 2);
v_moreLeancArgs_1461_ = lean_ctor_get(v_cfg_1456_, 3);
v_weakLeancArgs_1462_ = lean_ctor_get(v_cfg_1456_, 5);
v_moreLinkObjs_1463_ = lean_ctor_get(v_cfg_1456_, 6);
v_moreLinkLibs_1464_ = lean_ctor_get(v_cfg_1456_, 7);
v_moreLinkArgs_1465_ = lean_ctor_get(v_cfg_1456_, 8);
v_weakLinkArgs_1466_ = lean_ctor_get(v_cfg_1456_, 9);
v_backend_1467_ = lean_ctor_get_uint8(v_cfg_1456_, sizeof(void*)*13 + 1);
v_platformIndependent_1468_ = lean_ctor_get(v_cfg_1456_, 10);
v_precompileImports_1469_ = lean_ctor_get_uint8(v_cfg_1456_, sizeof(void*)*13 + 2);
v_dynlibs_1470_ = lean_ctor_get(v_cfg_1456_, 11);
v_plugins_1471_ = lean_ctor_get(v_cfg_1456_, 12);
v_requiresModuleSystem_1472_ = lean_ctor_get_uint8(v_cfg_1456_, sizeof(void*)*13 + 3);
v_allowNonModules_1473_ = lean_ctor_get_uint8(v_cfg_1456_, sizeof(void*)*13 + 4);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_cfg_1456_);
if (v_isSharedCheck_1480_ == 0)
{
lean_object* v_unused_1481_; 
v_unused_1481_ = lean_ctor_get(v_cfg_1456_, 4);
lean_dec(v_unused_1481_);
v___x_1475_ = v_cfg_1456_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_plugins_1471_);
lean_inc(v_dynlibs_1470_);
lean_inc(v_platformIndependent_1468_);
lean_inc(v_weakLinkArgs_1466_);
lean_inc(v_moreLinkArgs_1465_);
lean_inc(v_moreLinkLibs_1464_);
lean_inc(v_moreLinkObjs_1463_);
lean_inc(v_weakLeancArgs_1462_);
lean_inc(v_moreLeancArgs_1461_);
lean_inc(v_weakLeanArgs_1460_);
lean_inc(v_moreLeanArgs_1459_);
lean_inc(v_leanOptions_1458_);
lean_dec(v_cfg_1456_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_val_1455_);
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_leanOptions_1458_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_moreLeanArgs_1459_);
lean_ctor_set(v_reuseFailAlloc_1479_, 2, v_weakLeanArgs_1460_);
lean_ctor_set(v_reuseFailAlloc_1479_, 3, v_moreLeancArgs_1461_);
lean_ctor_set(v_reuseFailAlloc_1479_, 4, v_val_1455_);
lean_ctor_set(v_reuseFailAlloc_1479_, 5, v_weakLeancArgs_1462_);
lean_ctor_set(v_reuseFailAlloc_1479_, 6, v_moreLinkObjs_1463_);
lean_ctor_set(v_reuseFailAlloc_1479_, 7, v_moreLinkLibs_1464_);
lean_ctor_set(v_reuseFailAlloc_1479_, 8, v_moreLinkArgs_1465_);
lean_ctor_set(v_reuseFailAlloc_1479_, 9, v_weakLinkArgs_1466_);
lean_ctor_set(v_reuseFailAlloc_1479_, 10, v_platformIndependent_1468_);
lean_ctor_set(v_reuseFailAlloc_1479_, 11, v_dynlibs_1470_);
lean_ctor_set(v_reuseFailAlloc_1479_, 12, v_plugins_1471_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*13, v_buildType_1457_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*13 + 1, v_backend_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*13 + 2, v_precompileImports_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1472_);
lean_ctor_set_uint8(v_reuseFailAlloc_1479_, sizeof(void*)*13 + 4, v_allowNonModules_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1482_, lean_object* v_cfg_1483_){
_start:
{
uint8_t v_buildType_1484_; lean_object* v_leanOptions_1485_; lean_object* v_moreLeanArgs_1486_; lean_object* v_weakLeanArgs_1487_; lean_object* v_moreLeancArgs_1488_; lean_object* v_moreServerOptions_1489_; lean_object* v_weakLeancArgs_1490_; lean_object* v_moreLinkObjs_1491_; lean_object* v_moreLinkLibs_1492_; lean_object* v_moreLinkArgs_1493_; lean_object* v_weakLinkArgs_1494_; uint8_t v_backend_1495_; lean_object* v_platformIndependent_1496_; uint8_t v_precompileImports_1497_; lean_object* v_dynlibs_1498_; lean_object* v_plugins_1499_; uint8_t v_requiresModuleSystem_1500_; uint8_t v_allowNonModules_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1509_; 
v_buildType_1484_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*13);
v_leanOptions_1485_ = lean_ctor_get(v_cfg_1483_, 0);
v_moreLeanArgs_1486_ = lean_ctor_get(v_cfg_1483_, 1);
v_weakLeanArgs_1487_ = lean_ctor_get(v_cfg_1483_, 2);
v_moreLeancArgs_1488_ = lean_ctor_get(v_cfg_1483_, 3);
v_moreServerOptions_1489_ = lean_ctor_get(v_cfg_1483_, 4);
v_weakLeancArgs_1490_ = lean_ctor_get(v_cfg_1483_, 5);
v_moreLinkObjs_1491_ = lean_ctor_get(v_cfg_1483_, 6);
v_moreLinkLibs_1492_ = lean_ctor_get(v_cfg_1483_, 7);
v_moreLinkArgs_1493_ = lean_ctor_get(v_cfg_1483_, 8);
v_weakLinkArgs_1494_ = lean_ctor_get(v_cfg_1483_, 9);
v_backend_1495_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*13 + 1);
v_platformIndependent_1496_ = lean_ctor_get(v_cfg_1483_, 10);
v_precompileImports_1497_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*13 + 2);
v_dynlibs_1498_ = lean_ctor_get(v_cfg_1483_, 11);
v_plugins_1499_ = lean_ctor_get(v_cfg_1483_, 12);
v_requiresModuleSystem_1500_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*13 + 3);
v_allowNonModules_1501_ = lean_ctor_get_uint8(v_cfg_1483_, sizeof(void*)*13 + 4);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_cfg_1483_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1503_ = v_cfg_1483_;
v_isShared_1504_ = v_isSharedCheck_1509_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_plugins_1499_);
lean_inc(v_dynlibs_1498_);
lean_inc(v_platformIndependent_1496_);
lean_inc(v_weakLinkArgs_1494_);
lean_inc(v_moreLinkArgs_1493_);
lean_inc(v_moreLinkLibs_1492_);
lean_inc(v_moreLinkObjs_1491_);
lean_inc(v_weakLeancArgs_1490_);
lean_inc(v_moreServerOptions_1489_);
lean_inc(v_moreLeancArgs_1488_);
lean_inc(v_weakLeanArgs_1487_);
lean_inc(v_moreLeanArgs_1486_);
lean_inc(v_leanOptions_1485_);
lean_dec(v_cfg_1483_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1509_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
v___x_1505_ = lean_apply_1(v_f_1482_, v_moreServerOptions_1489_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v___x_1505_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_leanOptions_1485_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_moreLeanArgs_1486_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_weakLeanArgs_1487_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_moreLeancArgs_1488_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1508_, 5, v_weakLeancArgs_1490_);
lean_ctor_set(v_reuseFailAlloc_1508_, 6, v_moreLinkObjs_1491_);
lean_ctor_set(v_reuseFailAlloc_1508_, 7, v_moreLinkLibs_1492_);
lean_ctor_set(v_reuseFailAlloc_1508_, 8, v_moreLinkArgs_1493_);
lean_ctor_set(v_reuseFailAlloc_1508_, 9, v_weakLinkArgs_1494_);
lean_ctor_set(v_reuseFailAlloc_1508_, 10, v_platformIndependent_1496_);
lean_ctor_set(v_reuseFailAlloc_1508_, 11, v_dynlibs_1498_);
lean_ctor_set(v_reuseFailAlloc_1508_, 12, v_plugins_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*13, v_buildType_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*13 + 1, v_backend_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*13 + 2, v_precompileImports_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1500_);
lean_ctor_set_uint8(v_reuseFailAlloc_1508_, sizeof(void*)*13 + 4, v_allowNonModules_1501_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1520_){
_start:
{
lean_object* v_weakLeancArgs_1521_; 
v_weakLeancArgs_1521_ = lean_ctor_get(v_cfg_1520_, 5);
lean_inc_ref(v_weakLeancArgs_1521_);
return v_weakLeancArgs_1521_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1522_);
lean_dec_ref(v_cfg_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1524_, lean_object* v_cfg_1525_){
_start:
{
uint8_t v_buildType_1526_; lean_object* v_leanOptions_1527_; lean_object* v_moreLeanArgs_1528_; lean_object* v_weakLeanArgs_1529_; lean_object* v_moreLeancArgs_1530_; lean_object* v_moreServerOptions_1531_; lean_object* v_moreLinkObjs_1532_; lean_object* v_moreLinkLibs_1533_; lean_object* v_moreLinkArgs_1534_; lean_object* v_weakLinkArgs_1535_; uint8_t v_backend_1536_; lean_object* v_platformIndependent_1537_; uint8_t v_precompileImports_1538_; lean_object* v_dynlibs_1539_; lean_object* v_plugins_1540_; uint8_t v_requiresModuleSystem_1541_; uint8_t v_allowNonModules_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
v_buildType_1526_ = lean_ctor_get_uint8(v_cfg_1525_, sizeof(void*)*13);
v_leanOptions_1527_ = lean_ctor_get(v_cfg_1525_, 0);
v_moreLeanArgs_1528_ = lean_ctor_get(v_cfg_1525_, 1);
v_weakLeanArgs_1529_ = lean_ctor_get(v_cfg_1525_, 2);
v_moreLeancArgs_1530_ = lean_ctor_get(v_cfg_1525_, 3);
v_moreServerOptions_1531_ = lean_ctor_get(v_cfg_1525_, 4);
v_moreLinkObjs_1532_ = lean_ctor_get(v_cfg_1525_, 6);
v_moreLinkLibs_1533_ = lean_ctor_get(v_cfg_1525_, 7);
v_moreLinkArgs_1534_ = lean_ctor_get(v_cfg_1525_, 8);
v_weakLinkArgs_1535_ = lean_ctor_get(v_cfg_1525_, 9);
v_backend_1536_ = lean_ctor_get_uint8(v_cfg_1525_, sizeof(void*)*13 + 1);
v_platformIndependent_1537_ = lean_ctor_get(v_cfg_1525_, 10);
v_precompileImports_1538_ = lean_ctor_get_uint8(v_cfg_1525_, sizeof(void*)*13 + 2);
v_dynlibs_1539_ = lean_ctor_get(v_cfg_1525_, 11);
v_plugins_1540_ = lean_ctor_get(v_cfg_1525_, 12);
v_requiresModuleSystem_1541_ = lean_ctor_get_uint8(v_cfg_1525_, sizeof(void*)*13 + 3);
v_allowNonModules_1542_ = lean_ctor_get_uint8(v_cfg_1525_, sizeof(void*)*13 + 4);
v_isSharedCheck_1549_ = !lean_is_exclusive(v_cfg_1525_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v_cfg_1525_, 5);
lean_dec(v_unused_1550_);
v___x_1544_ = v_cfg_1525_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_plugins_1540_);
lean_inc(v_dynlibs_1539_);
lean_inc(v_platformIndependent_1537_);
lean_inc(v_weakLinkArgs_1535_);
lean_inc(v_moreLinkArgs_1534_);
lean_inc(v_moreLinkLibs_1533_);
lean_inc(v_moreLinkObjs_1532_);
lean_inc(v_moreServerOptions_1531_);
lean_inc(v_moreLeancArgs_1530_);
lean_inc(v_weakLeanArgs_1529_);
lean_inc(v_moreLeanArgs_1528_);
lean_inc(v_leanOptions_1527_);
lean_dec(v_cfg_1525_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 5, v_val_1524_);
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_leanOptions_1527_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_moreLeanArgs_1528_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_weakLeanArgs_1529_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_moreLeancArgs_1530_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_moreServerOptions_1531_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v_val_1524_);
lean_ctor_set(v_reuseFailAlloc_1548_, 6, v_moreLinkObjs_1532_);
lean_ctor_set(v_reuseFailAlloc_1548_, 7, v_moreLinkLibs_1533_);
lean_ctor_set(v_reuseFailAlloc_1548_, 8, v_moreLinkArgs_1534_);
lean_ctor_set(v_reuseFailAlloc_1548_, 9, v_weakLinkArgs_1535_);
lean_ctor_set(v_reuseFailAlloc_1548_, 10, v_platformIndependent_1537_);
lean_ctor_set(v_reuseFailAlloc_1548_, 11, v_dynlibs_1539_);
lean_ctor_set(v_reuseFailAlloc_1548_, 12, v_plugins_1540_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*13, v_buildType_1526_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*13 + 1, v_backend_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*13 + 2, v_precompileImports_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1541_);
lean_ctor_set_uint8(v_reuseFailAlloc_1548_, sizeof(void*)*13 + 4, v_allowNonModules_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1551_, lean_object* v_cfg_1552_){
_start:
{
uint8_t v_buildType_1553_; lean_object* v_leanOptions_1554_; lean_object* v_moreLeanArgs_1555_; lean_object* v_weakLeanArgs_1556_; lean_object* v_moreLeancArgs_1557_; lean_object* v_moreServerOptions_1558_; lean_object* v_weakLeancArgs_1559_; lean_object* v_moreLinkObjs_1560_; lean_object* v_moreLinkLibs_1561_; lean_object* v_moreLinkArgs_1562_; lean_object* v_weakLinkArgs_1563_; uint8_t v_backend_1564_; lean_object* v_platformIndependent_1565_; uint8_t v_precompileImports_1566_; lean_object* v_dynlibs_1567_; lean_object* v_plugins_1568_; uint8_t v_requiresModuleSystem_1569_; uint8_t v_allowNonModules_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1578_; 
v_buildType_1553_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*13);
v_leanOptions_1554_ = lean_ctor_get(v_cfg_1552_, 0);
v_moreLeanArgs_1555_ = lean_ctor_get(v_cfg_1552_, 1);
v_weakLeanArgs_1556_ = lean_ctor_get(v_cfg_1552_, 2);
v_moreLeancArgs_1557_ = lean_ctor_get(v_cfg_1552_, 3);
v_moreServerOptions_1558_ = lean_ctor_get(v_cfg_1552_, 4);
v_weakLeancArgs_1559_ = lean_ctor_get(v_cfg_1552_, 5);
v_moreLinkObjs_1560_ = lean_ctor_get(v_cfg_1552_, 6);
v_moreLinkLibs_1561_ = lean_ctor_get(v_cfg_1552_, 7);
v_moreLinkArgs_1562_ = lean_ctor_get(v_cfg_1552_, 8);
v_weakLinkArgs_1563_ = lean_ctor_get(v_cfg_1552_, 9);
v_backend_1564_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*13 + 1);
v_platformIndependent_1565_ = lean_ctor_get(v_cfg_1552_, 10);
v_precompileImports_1566_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*13 + 2);
v_dynlibs_1567_ = lean_ctor_get(v_cfg_1552_, 11);
v_plugins_1568_ = lean_ctor_get(v_cfg_1552_, 12);
v_requiresModuleSystem_1569_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*13 + 3);
v_allowNonModules_1570_ = lean_ctor_get_uint8(v_cfg_1552_, sizeof(void*)*13 + 4);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_cfg_1552_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1572_ = v_cfg_1552_;
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_plugins_1568_);
lean_inc(v_dynlibs_1567_);
lean_inc(v_platformIndependent_1565_);
lean_inc(v_weakLinkArgs_1563_);
lean_inc(v_moreLinkArgs_1562_);
lean_inc(v_moreLinkLibs_1561_);
lean_inc(v_moreLinkObjs_1560_);
lean_inc(v_weakLeancArgs_1559_);
lean_inc(v_moreServerOptions_1558_);
lean_inc(v_moreLeancArgs_1557_);
lean_inc(v_weakLeanArgs_1556_);
lean_inc(v_moreLeanArgs_1555_);
lean_inc(v_leanOptions_1554_);
lean_dec(v_cfg_1552_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1578_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_apply_1(v_f_1551_, v_weakLeancArgs_1559_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 5, v___x_1574_);
v___x_1576_ = v___x_1572_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_leanOptions_1554_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_moreLeanArgs_1555_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_weakLeanArgs_1556_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_moreLeancArgs_1557_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v_moreServerOptions_1558_);
lean_ctor_set(v_reuseFailAlloc_1577_, 5, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1577_, 6, v_moreLinkObjs_1560_);
lean_ctor_set(v_reuseFailAlloc_1577_, 7, v_moreLinkLibs_1561_);
lean_ctor_set(v_reuseFailAlloc_1577_, 8, v_moreLinkArgs_1562_);
lean_ctor_set(v_reuseFailAlloc_1577_, 9, v_weakLinkArgs_1563_);
lean_ctor_set(v_reuseFailAlloc_1577_, 10, v_platformIndependent_1565_);
lean_ctor_set(v_reuseFailAlloc_1577_, 11, v_dynlibs_1567_);
lean_ctor_set(v_reuseFailAlloc_1577_, 12, v_plugins_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1577_, sizeof(void*)*13, v_buildType_1553_);
lean_ctor_set_uint8(v_reuseFailAlloc_1577_, sizeof(void*)*13 + 1, v_backend_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1577_, sizeof(void*)*13 + 2, v_precompileImports_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1577_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1569_);
lean_ctor_set_uint8(v_reuseFailAlloc_1577_, sizeof(void*)*13 + 4, v_allowNonModules_1570_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1589_){
_start:
{
lean_object* v_moreLinkObjs_1590_; 
v_moreLinkObjs_1590_ = lean_ctor_get(v_cfg_1589_, 6);
lean_inc_ref(v_moreLinkObjs_1590_);
return v_moreLinkObjs_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1591_);
lean_dec_ref(v_cfg_1591_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1593_, lean_object* v_cfg_1594_){
_start:
{
uint8_t v_buildType_1595_; lean_object* v_leanOptions_1596_; lean_object* v_moreLeanArgs_1597_; lean_object* v_weakLeanArgs_1598_; lean_object* v_moreLeancArgs_1599_; lean_object* v_moreServerOptions_1600_; lean_object* v_weakLeancArgs_1601_; lean_object* v_moreLinkLibs_1602_; lean_object* v_moreLinkArgs_1603_; lean_object* v_weakLinkArgs_1604_; uint8_t v_backend_1605_; lean_object* v_platformIndependent_1606_; uint8_t v_precompileImports_1607_; lean_object* v_dynlibs_1608_; lean_object* v_plugins_1609_; uint8_t v_requiresModuleSystem_1610_; uint8_t v_allowNonModules_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
v_buildType_1595_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*13);
v_leanOptions_1596_ = lean_ctor_get(v_cfg_1594_, 0);
v_moreLeanArgs_1597_ = lean_ctor_get(v_cfg_1594_, 1);
v_weakLeanArgs_1598_ = lean_ctor_get(v_cfg_1594_, 2);
v_moreLeancArgs_1599_ = lean_ctor_get(v_cfg_1594_, 3);
v_moreServerOptions_1600_ = lean_ctor_get(v_cfg_1594_, 4);
v_weakLeancArgs_1601_ = lean_ctor_get(v_cfg_1594_, 5);
v_moreLinkLibs_1602_ = lean_ctor_get(v_cfg_1594_, 7);
v_moreLinkArgs_1603_ = lean_ctor_get(v_cfg_1594_, 8);
v_weakLinkArgs_1604_ = lean_ctor_get(v_cfg_1594_, 9);
v_backend_1605_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*13 + 1);
v_platformIndependent_1606_ = lean_ctor_get(v_cfg_1594_, 10);
v_precompileImports_1607_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*13 + 2);
v_dynlibs_1608_ = lean_ctor_get(v_cfg_1594_, 11);
v_plugins_1609_ = lean_ctor_get(v_cfg_1594_, 12);
v_requiresModuleSystem_1610_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*13 + 3);
v_allowNonModules_1611_ = lean_ctor_get_uint8(v_cfg_1594_, sizeof(void*)*13 + 4);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_cfg_1594_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v_cfg_1594_, 6);
lean_dec(v_unused_1619_);
v___x_1613_ = v_cfg_1594_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_plugins_1609_);
lean_inc(v_dynlibs_1608_);
lean_inc(v_platformIndependent_1606_);
lean_inc(v_weakLinkArgs_1604_);
lean_inc(v_moreLinkArgs_1603_);
lean_inc(v_moreLinkLibs_1602_);
lean_inc(v_weakLeancArgs_1601_);
lean_inc(v_moreServerOptions_1600_);
lean_inc(v_moreLeancArgs_1599_);
lean_inc(v_weakLeanArgs_1598_);
lean_inc(v_moreLeanArgs_1597_);
lean_inc(v_leanOptions_1596_);
lean_dec(v_cfg_1594_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 6, v_val_1593_);
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_leanOptions_1596_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_moreLeanArgs_1597_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_weakLeanArgs_1598_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_moreLeancArgs_1599_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_moreServerOptions_1600_);
lean_ctor_set(v_reuseFailAlloc_1617_, 5, v_weakLeancArgs_1601_);
lean_ctor_set(v_reuseFailAlloc_1617_, 6, v_val_1593_);
lean_ctor_set(v_reuseFailAlloc_1617_, 7, v_moreLinkLibs_1602_);
lean_ctor_set(v_reuseFailAlloc_1617_, 8, v_moreLinkArgs_1603_);
lean_ctor_set(v_reuseFailAlloc_1617_, 9, v_weakLinkArgs_1604_);
lean_ctor_set(v_reuseFailAlloc_1617_, 10, v_platformIndependent_1606_);
lean_ctor_set(v_reuseFailAlloc_1617_, 11, v_dynlibs_1608_);
lean_ctor_set(v_reuseFailAlloc_1617_, 12, v_plugins_1609_);
lean_ctor_set_uint8(v_reuseFailAlloc_1617_, sizeof(void*)*13, v_buildType_1595_);
lean_ctor_set_uint8(v_reuseFailAlloc_1617_, sizeof(void*)*13 + 1, v_backend_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1617_, sizeof(void*)*13 + 2, v_precompileImports_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1617_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1617_, sizeof(void*)*13 + 4, v_allowNonModules_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1620_, lean_object* v_cfg_1621_){
_start:
{
uint8_t v_buildType_1622_; lean_object* v_leanOptions_1623_; lean_object* v_moreLeanArgs_1624_; lean_object* v_weakLeanArgs_1625_; lean_object* v_moreLeancArgs_1626_; lean_object* v_moreServerOptions_1627_; lean_object* v_weakLeancArgs_1628_; lean_object* v_moreLinkObjs_1629_; lean_object* v_moreLinkLibs_1630_; lean_object* v_moreLinkArgs_1631_; lean_object* v_weakLinkArgs_1632_; uint8_t v_backend_1633_; lean_object* v_platformIndependent_1634_; uint8_t v_precompileImports_1635_; lean_object* v_dynlibs_1636_; lean_object* v_plugins_1637_; uint8_t v_requiresModuleSystem_1638_; uint8_t v_allowNonModules_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1647_; 
v_buildType_1622_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*13);
v_leanOptions_1623_ = lean_ctor_get(v_cfg_1621_, 0);
v_moreLeanArgs_1624_ = lean_ctor_get(v_cfg_1621_, 1);
v_weakLeanArgs_1625_ = lean_ctor_get(v_cfg_1621_, 2);
v_moreLeancArgs_1626_ = lean_ctor_get(v_cfg_1621_, 3);
v_moreServerOptions_1627_ = lean_ctor_get(v_cfg_1621_, 4);
v_weakLeancArgs_1628_ = lean_ctor_get(v_cfg_1621_, 5);
v_moreLinkObjs_1629_ = lean_ctor_get(v_cfg_1621_, 6);
v_moreLinkLibs_1630_ = lean_ctor_get(v_cfg_1621_, 7);
v_moreLinkArgs_1631_ = lean_ctor_get(v_cfg_1621_, 8);
v_weakLinkArgs_1632_ = lean_ctor_get(v_cfg_1621_, 9);
v_backend_1633_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*13 + 1);
v_platformIndependent_1634_ = lean_ctor_get(v_cfg_1621_, 10);
v_precompileImports_1635_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*13 + 2);
v_dynlibs_1636_ = lean_ctor_get(v_cfg_1621_, 11);
v_plugins_1637_ = lean_ctor_get(v_cfg_1621_, 12);
v_requiresModuleSystem_1638_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*13 + 3);
v_allowNonModules_1639_ = lean_ctor_get_uint8(v_cfg_1621_, sizeof(void*)*13 + 4);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_cfg_1621_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1641_ = v_cfg_1621_;
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_plugins_1637_);
lean_inc(v_dynlibs_1636_);
lean_inc(v_platformIndependent_1634_);
lean_inc(v_weakLinkArgs_1632_);
lean_inc(v_moreLinkArgs_1631_);
lean_inc(v_moreLinkLibs_1630_);
lean_inc(v_moreLinkObjs_1629_);
lean_inc(v_weakLeancArgs_1628_);
lean_inc(v_moreServerOptions_1627_);
lean_inc(v_moreLeancArgs_1626_);
lean_inc(v_weakLeanArgs_1625_);
lean_inc(v_moreLeanArgs_1624_);
lean_inc(v_leanOptions_1623_);
lean_dec(v_cfg_1621_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1647_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_apply_1(v_f_1620_, v_moreLinkObjs_1629_);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 6, v___x_1643_);
v___x_1645_ = v___x_1641_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_leanOptions_1623_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_moreLeanArgs_1624_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_weakLeanArgs_1625_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_moreLeancArgs_1626_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v_moreServerOptions_1627_);
lean_ctor_set(v_reuseFailAlloc_1646_, 5, v_weakLeancArgs_1628_);
lean_ctor_set(v_reuseFailAlloc_1646_, 6, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1646_, 7, v_moreLinkLibs_1630_);
lean_ctor_set(v_reuseFailAlloc_1646_, 8, v_moreLinkArgs_1631_);
lean_ctor_set(v_reuseFailAlloc_1646_, 9, v_weakLinkArgs_1632_);
lean_ctor_set(v_reuseFailAlloc_1646_, 10, v_platformIndependent_1634_);
lean_ctor_set(v_reuseFailAlloc_1646_, 11, v_dynlibs_1636_);
lean_ctor_set(v_reuseFailAlloc_1646_, 12, v_plugins_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1646_, sizeof(void*)*13, v_buildType_1622_);
lean_ctor_set_uint8(v_reuseFailAlloc_1646_, sizeof(void*)*13 + 1, v_backend_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1646_, sizeof(void*)*13 + 2, v_precompileImports_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1646_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1638_);
lean_ctor_set_uint8(v_reuseFailAlloc_1646_, sizeof(void*)*13 + 4, v_allowNonModules_1639_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1652_);
lean_dec_ref(v_x_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1665_){
_start:
{
lean_object* v_moreLinkLibs_1666_; 
v_moreLinkLibs_1666_ = lean_ctor_get(v_cfg_1665_, 7);
lean_inc_ref(v_moreLinkLibs_1666_);
return v_moreLinkLibs_1666_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1667_);
lean_dec_ref(v_cfg_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1669_, lean_object* v_cfg_1670_){
_start:
{
uint8_t v_buildType_1671_; lean_object* v_leanOptions_1672_; lean_object* v_moreLeanArgs_1673_; lean_object* v_weakLeanArgs_1674_; lean_object* v_moreLeancArgs_1675_; lean_object* v_moreServerOptions_1676_; lean_object* v_weakLeancArgs_1677_; lean_object* v_moreLinkObjs_1678_; lean_object* v_moreLinkArgs_1679_; lean_object* v_weakLinkArgs_1680_; uint8_t v_backend_1681_; lean_object* v_platformIndependent_1682_; uint8_t v_precompileImports_1683_; lean_object* v_dynlibs_1684_; lean_object* v_plugins_1685_; uint8_t v_requiresModuleSystem_1686_; uint8_t v_allowNonModules_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
v_buildType_1671_ = lean_ctor_get_uint8(v_cfg_1670_, sizeof(void*)*13);
v_leanOptions_1672_ = lean_ctor_get(v_cfg_1670_, 0);
v_moreLeanArgs_1673_ = lean_ctor_get(v_cfg_1670_, 1);
v_weakLeanArgs_1674_ = lean_ctor_get(v_cfg_1670_, 2);
v_moreLeancArgs_1675_ = lean_ctor_get(v_cfg_1670_, 3);
v_moreServerOptions_1676_ = lean_ctor_get(v_cfg_1670_, 4);
v_weakLeancArgs_1677_ = lean_ctor_get(v_cfg_1670_, 5);
v_moreLinkObjs_1678_ = lean_ctor_get(v_cfg_1670_, 6);
v_moreLinkArgs_1679_ = lean_ctor_get(v_cfg_1670_, 8);
v_weakLinkArgs_1680_ = lean_ctor_get(v_cfg_1670_, 9);
v_backend_1681_ = lean_ctor_get_uint8(v_cfg_1670_, sizeof(void*)*13 + 1);
v_platformIndependent_1682_ = lean_ctor_get(v_cfg_1670_, 10);
v_precompileImports_1683_ = lean_ctor_get_uint8(v_cfg_1670_, sizeof(void*)*13 + 2);
v_dynlibs_1684_ = lean_ctor_get(v_cfg_1670_, 11);
v_plugins_1685_ = lean_ctor_get(v_cfg_1670_, 12);
v_requiresModuleSystem_1686_ = lean_ctor_get_uint8(v_cfg_1670_, sizeof(void*)*13 + 3);
v_allowNonModules_1687_ = lean_ctor_get_uint8(v_cfg_1670_, sizeof(void*)*13 + 4);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_cfg_1670_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v_cfg_1670_, 7);
lean_dec(v_unused_1695_);
v___x_1689_ = v_cfg_1670_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_plugins_1685_);
lean_inc(v_dynlibs_1684_);
lean_inc(v_platformIndependent_1682_);
lean_inc(v_weakLinkArgs_1680_);
lean_inc(v_moreLinkArgs_1679_);
lean_inc(v_moreLinkObjs_1678_);
lean_inc(v_weakLeancArgs_1677_);
lean_inc(v_moreServerOptions_1676_);
lean_inc(v_moreLeancArgs_1675_);
lean_inc(v_weakLeanArgs_1674_);
lean_inc(v_moreLeanArgs_1673_);
lean_inc(v_leanOptions_1672_);
lean_dec(v_cfg_1670_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 7, v_val_1669_);
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_leanOptions_1672_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_moreLeanArgs_1673_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_weakLeanArgs_1674_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_moreLeancArgs_1675_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_moreServerOptions_1676_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_weakLeancArgs_1677_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_moreLinkObjs_1678_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_val_1669_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_moreLinkArgs_1679_);
lean_ctor_set(v_reuseFailAlloc_1693_, 9, v_weakLinkArgs_1680_);
lean_ctor_set(v_reuseFailAlloc_1693_, 10, v_platformIndependent_1682_);
lean_ctor_set(v_reuseFailAlloc_1693_, 11, v_dynlibs_1684_);
lean_ctor_set(v_reuseFailAlloc_1693_, 12, v_plugins_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13, v_buildType_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13 + 1, v_backend_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13 + 2, v_precompileImports_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1686_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13 + 4, v_allowNonModules_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1696_, lean_object* v_cfg_1697_){
_start:
{
uint8_t v_buildType_1698_; lean_object* v_leanOptions_1699_; lean_object* v_moreLeanArgs_1700_; lean_object* v_weakLeanArgs_1701_; lean_object* v_moreLeancArgs_1702_; lean_object* v_moreServerOptions_1703_; lean_object* v_weakLeancArgs_1704_; lean_object* v_moreLinkObjs_1705_; lean_object* v_moreLinkLibs_1706_; lean_object* v_moreLinkArgs_1707_; lean_object* v_weakLinkArgs_1708_; uint8_t v_backend_1709_; lean_object* v_platformIndependent_1710_; uint8_t v_precompileImports_1711_; lean_object* v_dynlibs_1712_; lean_object* v_plugins_1713_; uint8_t v_requiresModuleSystem_1714_; uint8_t v_allowNonModules_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
v_buildType_1698_ = lean_ctor_get_uint8(v_cfg_1697_, sizeof(void*)*13);
v_leanOptions_1699_ = lean_ctor_get(v_cfg_1697_, 0);
v_moreLeanArgs_1700_ = lean_ctor_get(v_cfg_1697_, 1);
v_weakLeanArgs_1701_ = lean_ctor_get(v_cfg_1697_, 2);
v_moreLeancArgs_1702_ = lean_ctor_get(v_cfg_1697_, 3);
v_moreServerOptions_1703_ = lean_ctor_get(v_cfg_1697_, 4);
v_weakLeancArgs_1704_ = lean_ctor_get(v_cfg_1697_, 5);
v_moreLinkObjs_1705_ = lean_ctor_get(v_cfg_1697_, 6);
v_moreLinkLibs_1706_ = lean_ctor_get(v_cfg_1697_, 7);
v_moreLinkArgs_1707_ = lean_ctor_get(v_cfg_1697_, 8);
v_weakLinkArgs_1708_ = lean_ctor_get(v_cfg_1697_, 9);
v_backend_1709_ = lean_ctor_get_uint8(v_cfg_1697_, sizeof(void*)*13 + 1);
v_platformIndependent_1710_ = lean_ctor_get(v_cfg_1697_, 10);
v_precompileImports_1711_ = lean_ctor_get_uint8(v_cfg_1697_, sizeof(void*)*13 + 2);
v_dynlibs_1712_ = lean_ctor_get(v_cfg_1697_, 11);
v_plugins_1713_ = lean_ctor_get(v_cfg_1697_, 12);
v_requiresModuleSystem_1714_ = lean_ctor_get_uint8(v_cfg_1697_, sizeof(void*)*13 + 3);
v_allowNonModules_1715_ = lean_ctor_get_uint8(v_cfg_1697_, sizeof(void*)*13 + 4);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_cfg_1697_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1717_ = v_cfg_1697_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_plugins_1713_);
lean_inc(v_dynlibs_1712_);
lean_inc(v_platformIndependent_1710_);
lean_inc(v_weakLinkArgs_1708_);
lean_inc(v_moreLinkArgs_1707_);
lean_inc(v_moreLinkLibs_1706_);
lean_inc(v_moreLinkObjs_1705_);
lean_inc(v_weakLeancArgs_1704_);
lean_inc(v_moreServerOptions_1703_);
lean_inc(v_moreLeancArgs_1702_);
lean_inc(v_weakLeanArgs_1701_);
lean_inc(v_moreLeanArgs_1700_);
lean_inc(v_leanOptions_1699_);
lean_dec(v_cfg_1697_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = lean_apply_1(v_f_1696_, v_moreLinkLibs_1706_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 7, v___x_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_leanOptions_1699_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_moreLeanArgs_1700_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_weakLeanArgs_1701_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_moreLeancArgs_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_moreServerOptions_1703_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_weakLeancArgs_1704_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_moreLinkObjs_1705_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_moreLinkArgs_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 9, v_weakLinkArgs_1708_);
lean_ctor_set(v_reuseFailAlloc_1722_, 10, v_platformIndependent_1710_);
lean_ctor_set(v_reuseFailAlloc_1722_, 11, v_dynlibs_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 12, v_plugins_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13, v_buildType_1698_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13 + 1, v_backend_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13 + 2, v_precompileImports_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13 + 4, v_allowNonModules_1715_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1734_){
_start:
{
lean_object* v_moreLinkArgs_1735_; 
v_moreLinkArgs_1735_ = lean_ctor_get(v_cfg_1734_, 8);
lean_inc_ref(v_moreLinkArgs_1735_);
return v_moreLinkArgs_1735_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1736_);
lean_dec_ref(v_cfg_1736_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1738_, lean_object* v_cfg_1739_){
_start:
{
uint8_t v_buildType_1740_; lean_object* v_leanOptions_1741_; lean_object* v_moreLeanArgs_1742_; lean_object* v_weakLeanArgs_1743_; lean_object* v_moreLeancArgs_1744_; lean_object* v_moreServerOptions_1745_; lean_object* v_weakLeancArgs_1746_; lean_object* v_moreLinkObjs_1747_; lean_object* v_moreLinkLibs_1748_; lean_object* v_weakLinkArgs_1749_; uint8_t v_backend_1750_; lean_object* v_platformIndependent_1751_; uint8_t v_precompileImports_1752_; lean_object* v_dynlibs_1753_; lean_object* v_plugins_1754_; uint8_t v_requiresModuleSystem_1755_; uint8_t v_allowNonModules_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
v_buildType_1740_ = lean_ctor_get_uint8(v_cfg_1739_, sizeof(void*)*13);
v_leanOptions_1741_ = lean_ctor_get(v_cfg_1739_, 0);
v_moreLeanArgs_1742_ = lean_ctor_get(v_cfg_1739_, 1);
v_weakLeanArgs_1743_ = lean_ctor_get(v_cfg_1739_, 2);
v_moreLeancArgs_1744_ = lean_ctor_get(v_cfg_1739_, 3);
v_moreServerOptions_1745_ = lean_ctor_get(v_cfg_1739_, 4);
v_weakLeancArgs_1746_ = lean_ctor_get(v_cfg_1739_, 5);
v_moreLinkObjs_1747_ = lean_ctor_get(v_cfg_1739_, 6);
v_moreLinkLibs_1748_ = lean_ctor_get(v_cfg_1739_, 7);
v_weakLinkArgs_1749_ = lean_ctor_get(v_cfg_1739_, 9);
v_backend_1750_ = lean_ctor_get_uint8(v_cfg_1739_, sizeof(void*)*13 + 1);
v_platformIndependent_1751_ = lean_ctor_get(v_cfg_1739_, 10);
v_precompileImports_1752_ = lean_ctor_get_uint8(v_cfg_1739_, sizeof(void*)*13 + 2);
v_dynlibs_1753_ = lean_ctor_get(v_cfg_1739_, 11);
v_plugins_1754_ = lean_ctor_get(v_cfg_1739_, 12);
v_requiresModuleSystem_1755_ = lean_ctor_get_uint8(v_cfg_1739_, sizeof(void*)*13 + 3);
v_allowNonModules_1756_ = lean_ctor_get_uint8(v_cfg_1739_, sizeof(void*)*13 + 4);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_cfg_1739_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v_cfg_1739_, 8);
lean_dec(v_unused_1764_);
v___x_1758_ = v_cfg_1739_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_plugins_1754_);
lean_inc(v_dynlibs_1753_);
lean_inc(v_platformIndependent_1751_);
lean_inc(v_weakLinkArgs_1749_);
lean_inc(v_moreLinkLibs_1748_);
lean_inc(v_moreLinkObjs_1747_);
lean_inc(v_weakLeancArgs_1746_);
lean_inc(v_moreServerOptions_1745_);
lean_inc(v_moreLeancArgs_1744_);
lean_inc(v_weakLeanArgs_1743_);
lean_inc(v_moreLeanArgs_1742_);
lean_inc(v_leanOptions_1741_);
lean_dec(v_cfg_1739_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 8, v_val_1738_);
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_leanOptions_1741_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_moreLeanArgs_1742_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_weakLeanArgs_1743_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_moreLeancArgs_1744_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_moreServerOptions_1745_);
lean_ctor_set(v_reuseFailAlloc_1762_, 5, v_weakLeancArgs_1746_);
lean_ctor_set(v_reuseFailAlloc_1762_, 6, v_moreLinkObjs_1747_);
lean_ctor_set(v_reuseFailAlloc_1762_, 7, v_moreLinkLibs_1748_);
lean_ctor_set(v_reuseFailAlloc_1762_, 8, v_val_1738_);
lean_ctor_set(v_reuseFailAlloc_1762_, 9, v_weakLinkArgs_1749_);
lean_ctor_set(v_reuseFailAlloc_1762_, 10, v_platformIndependent_1751_);
lean_ctor_set(v_reuseFailAlloc_1762_, 11, v_dynlibs_1753_);
lean_ctor_set(v_reuseFailAlloc_1762_, 12, v_plugins_1754_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*13, v_buildType_1740_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*13 + 1, v_backend_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*13 + 2, v_precompileImports_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1755_);
lean_ctor_set_uint8(v_reuseFailAlloc_1762_, sizeof(void*)*13 + 4, v_allowNonModules_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1765_, lean_object* v_cfg_1766_){
_start:
{
uint8_t v_buildType_1767_; lean_object* v_leanOptions_1768_; lean_object* v_moreLeanArgs_1769_; lean_object* v_weakLeanArgs_1770_; lean_object* v_moreLeancArgs_1771_; lean_object* v_moreServerOptions_1772_; lean_object* v_weakLeancArgs_1773_; lean_object* v_moreLinkObjs_1774_; lean_object* v_moreLinkLibs_1775_; lean_object* v_moreLinkArgs_1776_; lean_object* v_weakLinkArgs_1777_; uint8_t v_backend_1778_; lean_object* v_platformIndependent_1779_; uint8_t v_precompileImports_1780_; lean_object* v_dynlibs_1781_; lean_object* v_plugins_1782_; uint8_t v_requiresModuleSystem_1783_; uint8_t v_allowNonModules_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1792_; 
v_buildType_1767_ = lean_ctor_get_uint8(v_cfg_1766_, sizeof(void*)*13);
v_leanOptions_1768_ = lean_ctor_get(v_cfg_1766_, 0);
v_moreLeanArgs_1769_ = lean_ctor_get(v_cfg_1766_, 1);
v_weakLeanArgs_1770_ = lean_ctor_get(v_cfg_1766_, 2);
v_moreLeancArgs_1771_ = lean_ctor_get(v_cfg_1766_, 3);
v_moreServerOptions_1772_ = lean_ctor_get(v_cfg_1766_, 4);
v_weakLeancArgs_1773_ = lean_ctor_get(v_cfg_1766_, 5);
v_moreLinkObjs_1774_ = lean_ctor_get(v_cfg_1766_, 6);
v_moreLinkLibs_1775_ = lean_ctor_get(v_cfg_1766_, 7);
v_moreLinkArgs_1776_ = lean_ctor_get(v_cfg_1766_, 8);
v_weakLinkArgs_1777_ = lean_ctor_get(v_cfg_1766_, 9);
v_backend_1778_ = lean_ctor_get_uint8(v_cfg_1766_, sizeof(void*)*13 + 1);
v_platformIndependent_1779_ = lean_ctor_get(v_cfg_1766_, 10);
v_precompileImports_1780_ = lean_ctor_get_uint8(v_cfg_1766_, sizeof(void*)*13 + 2);
v_dynlibs_1781_ = lean_ctor_get(v_cfg_1766_, 11);
v_plugins_1782_ = lean_ctor_get(v_cfg_1766_, 12);
v_requiresModuleSystem_1783_ = lean_ctor_get_uint8(v_cfg_1766_, sizeof(void*)*13 + 3);
v_allowNonModules_1784_ = lean_ctor_get_uint8(v_cfg_1766_, sizeof(void*)*13 + 4);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_cfg_1766_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1786_ = v_cfg_1766_;
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_plugins_1782_);
lean_inc(v_dynlibs_1781_);
lean_inc(v_platformIndependent_1779_);
lean_inc(v_weakLinkArgs_1777_);
lean_inc(v_moreLinkArgs_1776_);
lean_inc(v_moreLinkLibs_1775_);
lean_inc(v_moreLinkObjs_1774_);
lean_inc(v_weakLeancArgs_1773_);
lean_inc(v_moreServerOptions_1772_);
lean_inc(v_moreLeancArgs_1771_);
lean_inc(v_weakLeanArgs_1770_);
lean_inc(v_moreLeanArgs_1769_);
lean_inc(v_leanOptions_1768_);
lean_dec(v_cfg_1766_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1792_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v___x_1790_; 
v___x_1788_ = lean_apply_1(v_f_1765_, v_moreLinkArgs_1776_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 8, v___x_1788_);
v___x_1790_ = v___x_1786_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_leanOptions_1768_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_moreLeanArgs_1769_);
lean_ctor_set(v_reuseFailAlloc_1791_, 2, v_weakLeanArgs_1770_);
lean_ctor_set(v_reuseFailAlloc_1791_, 3, v_moreLeancArgs_1771_);
lean_ctor_set(v_reuseFailAlloc_1791_, 4, v_moreServerOptions_1772_);
lean_ctor_set(v_reuseFailAlloc_1791_, 5, v_weakLeancArgs_1773_);
lean_ctor_set(v_reuseFailAlloc_1791_, 6, v_moreLinkObjs_1774_);
lean_ctor_set(v_reuseFailAlloc_1791_, 7, v_moreLinkLibs_1775_);
lean_ctor_set(v_reuseFailAlloc_1791_, 8, v___x_1788_);
lean_ctor_set(v_reuseFailAlloc_1791_, 9, v_weakLinkArgs_1777_);
lean_ctor_set(v_reuseFailAlloc_1791_, 10, v_platformIndependent_1779_);
lean_ctor_set(v_reuseFailAlloc_1791_, 11, v_dynlibs_1781_);
lean_ctor_set(v_reuseFailAlloc_1791_, 12, v_plugins_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*13, v_buildType_1767_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*13 + 1, v_backend_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*13 + 2, v_precompileImports_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1791_, sizeof(void*)*13 + 4, v_allowNonModules_1784_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1803_){
_start:
{
lean_object* v_weakLinkArgs_1804_; 
v_weakLinkArgs_1804_ = lean_ctor_get(v_cfg_1803_, 9);
lean_inc_ref(v_weakLinkArgs_1804_);
return v_weakLinkArgs_1804_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1805_);
lean_dec_ref(v_cfg_1805_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1807_, lean_object* v_cfg_1808_){
_start:
{
uint8_t v_buildType_1809_; lean_object* v_leanOptions_1810_; lean_object* v_moreLeanArgs_1811_; lean_object* v_weakLeanArgs_1812_; lean_object* v_moreLeancArgs_1813_; lean_object* v_moreServerOptions_1814_; lean_object* v_weakLeancArgs_1815_; lean_object* v_moreLinkObjs_1816_; lean_object* v_moreLinkLibs_1817_; lean_object* v_moreLinkArgs_1818_; uint8_t v_backend_1819_; lean_object* v_platformIndependent_1820_; uint8_t v_precompileImports_1821_; lean_object* v_dynlibs_1822_; lean_object* v_plugins_1823_; uint8_t v_requiresModuleSystem_1824_; uint8_t v_allowNonModules_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
v_buildType_1809_ = lean_ctor_get_uint8(v_cfg_1808_, sizeof(void*)*13);
v_leanOptions_1810_ = lean_ctor_get(v_cfg_1808_, 0);
v_moreLeanArgs_1811_ = lean_ctor_get(v_cfg_1808_, 1);
v_weakLeanArgs_1812_ = lean_ctor_get(v_cfg_1808_, 2);
v_moreLeancArgs_1813_ = lean_ctor_get(v_cfg_1808_, 3);
v_moreServerOptions_1814_ = lean_ctor_get(v_cfg_1808_, 4);
v_weakLeancArgs_1815_ = lean_ctor_get(v_cfg_1808_, 5);
v_moreLinkObjs_1816_ = lean_ctor_get(v_cfg_1808_, 6);
v_moreLinkLibs_1817_ = lean_ctor_get(v_cfg_1808_, 7);
v_moreLinkArgs_1818_ = lean_ctor_get(v_cfg_1808_, 8);
v_backend_1819_ = lean_ctor_get_uint8(v_cfg_1808_, sizeof(void*)*13 + 1);
v_platformIndependent_1820_ = lean_ctor_get(v_cfg_1808_, 10);
v_precompileImports_1821_ = lean_ctor_get_uint8(v_cfg_1808_, sizeof(void*)*13 + 2);
v_dynlibs_1822_ = lean_ctor_get(v_cfg_1808_, 11);
v_plugins_1823_ = lean_ctor_get(v_cfg_1808_, 12);
v_requiresModuleSystem_1824_ = lean_ctor_get_uint8(v_cfg_1808_, sizeof(void*)*13 + 3);
v_allowNonModules_1825_ = lean_ctor_get_uint8(v_cfg_1808_, sizeof(void*)*13 + 4);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_cfg_1808_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v_cfg_1808_, 9);
lean_dec(v_unused_1833_);
v___x_1827_ = v_cfg_1808_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_plugins_1823_);
lean_inc(v_dynlibs_1822_);
lean_inc(v_platformIndependent_1820_);
lean_inc(v_moreLinkArgs_1818_);
lean_inc(v_moreLinkLibs_1817_);
lean_inc(v_moreLinkObjs_1816_);
lean_inc(v_weakLeancArgs_1815_);
lean_inc(v_moreServerOptions_1814_);
lean_inc(v_moreLeancArgs_1813_);
lean_inc(v_weakLeanArgs_1812_);
lean_inc(v_moreLeanArgs_1811_);
lean_inc(v_leanOptions_1810_);
lean_dec(v_cfg_1808_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 9, v_val_1807_);
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_leanOptions_1810_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_moreLeanArgs_1811_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_weakLeanArgs_1812_);
lean_ctor_set(v_reuseFailAlloc_1831_, 3, v_moreLeancArgs_1813_);
lean_ctor_set(v_reuseFailAlloc_1831_, 4, v_moreServerOptions_1814_);
lean_ctor_set(v_reuseFailAlloc_1831_, 5, v_weakLeancArgs_1815_);
lean_ctor_set(v_reuseFailAlloc_1831_, 6, v_moreLinkObjs_1816_);
lean_ctor_set(v_reuseFailAlloc_1831_, 7, v_moreLinkLibs_1817_);
lean_ctor_set(v_reuseFailAlloc_1831_, 8, v_moreLinkArgs_1818_);
lean_ctor_set(v_reuseFailAlloc_1831_, 9, v_val_1807_);
lean_ctor_set(v_reuseFailAlloc_1831_, 10, v_platformIndependent_1820_);
lean_ctor_set(v_reuseFailAlloc_1831_, 11, v_dynlibs_1822_);
lean_ctor_set(v_reuseFailAlloc_1831_, 12, v_plugins_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13, v_buildType_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 1, v_backend_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 2, v_precompileImports_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1831_, sizeof(void*)*13 + 4, v_allowNonModules_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1834_, lean_object* v_cfg_1835_){
_start:
{
uint8_t v_buildType_1836_; lean_object* v_leanOptions_1837_; lean_object* v_moreLeanArgs_1838_; lean_object* v_weakLeanArgs_1839_; lean_object* v_moreLeancArgs_1840_; lean_object* v_moreServerOptions_1841_; lean_object* v_weakLeancArgs_1842_; lean_object* v_moreLinkObjs_1843_; lean_object* v_moreLinkLibs_1844_; lean_object* v_moreLinkArgs_1845_; lean_object* v_weakLinkArgs_1846_; uint8_t v_backend_1847_; lean_object* v_platformIndependent_1848_; uint8_t v_precompileImports_1849_; lean_object* v_dynlibs_1850_; lean_object* v_plugins_1851_; uint8_t v_requiresModuleSystem_1852_; uint8_t v_allowNonModules_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1861_; 
v_buildType_1836_ = lean_ctor_get_uint8(v_cfg_1835_, sizeof(void*)*13);
v_leanOptions_1837_ = lean_ctor_get(v_cfg_1835_, 0);
v_moreLeanArgs_1838_ = lean_ctor_get(v_cfg_1835_, 1);
v_weakLeanArgs_1839_ = lean_ctor_get(v_cfg_1835_, 2);
v_moreLeancArgs_1840_ = lean_ctor_get(v_cfg_1835_, 3);
v_moreServerOptions_1841_ = lean_ctor_get(v_cfg_1835_, 4);
v_weakLeancArgs_1842_ = lean_ctor_get(v_cfg_1835_, 5);
v_moreLinkObjs_1843_ = lean_ctor_get(v_cfg_1835_, 6);
v_moreLinkLibs_1844_ = lean_ctor_get(v_cfg_1835_, 7);
v_moreLinkArgs_1845_ = lean_ctor_get(v_cfg_1835_, 8);
v_weakLinkArgs_1846_ = lean_ctor_get(v_cfg_1835_, 9);
v_backend_1847_ = lean_ctor_get_uint8(v_cfg_1835_, sizeof(void*)*13 + 1);
v_platformIndependent_1848_ = lean_ctor_get(v_cfg_1835_, 10);
v_precompileImports_1849_ = lean_ctor_get_uint8(v_cfg_1835_, sizeof(void*)*13 + 2);
v_dynlibs_1850_ = lean_ctor_get(v_cfg_1835_, 11);
v_plugins_1851_ = lean_ctor_get(v_cfg_1835_, 12);
v_requiresModuleSystem_1852_ = lean_ctor_get_uint8(v_cfg_1835_, sizeof(void*)*13 + 3);
v_allowNonModules_1853_ = lean_ctor_get_uint8(v_cfg_1835_, sizeof(void*)*13 + 4);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_cfg_1835_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1855_ = v_cfg_1835_;
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_plugins_1851_);
lean_inc(v_dynlibs_1850_);
lean_inc(v_platformIndependent_1848_);
lean_inc(v_weakLinkArgs_1846_);
lean_inc(v_moreLinkArgs_1845_);
lean_inc(v_moreLinkLibs_1844_);
lean_inc(v_moreLinkObjs_1843_);
lean_inc(v_weakLeancArgs_1842_);
lean_inc(v_moreServerOptions_1841_);
lean_inc(v_moreLeancArgs_1840_);
lean_inc(v_weakLeanArgs_1839_);
lean_inc(v_moreLeanArgs_1838_);
lean_inc(v_leanOptions_1837_);
lean_dec(v_cfg_1835_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1861_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1857_ = lean_apply_1(v_f_1834_, v_weakLinkArgs_1846_);
if (v_isShared_1856_ == 0)
{
lean_ctor_set(v___x_1855_, 9, v___x_1857_);
v___x_1859_ = v___x_1855_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_leanOptions_1837_);
lean_ctor_set(v_reuseFailAlloc_1860_, 1, v_moreLeanArgs_1838_);
lean_ctor_set(v_reuseFailAlloc_1860_, 2, v_weakLeanArgs_1839_);
lean_ctor_set(v_reuseFailAlloc_1860_, 3, v_moreLeancArgs_1840_);
lean_ctor_set(v_reuseFailAlloc_1860_, 4, v_moreServerOptions_1841_);
lean_ctor_set(v_reuseFailAlloc_1860_, 5, v_weakLeancArgs_1842_);
lean_ctor_set(v_reuseFailAlloc_1860_, 6, v_moreLinkObjs_1843_);
lean_ctor_set(v_reuseFailAlloc_1860_, 7, v_moreLinkLibs_1844_);
lean_ctor_set(v_reuseFailAlloc_1860_, 8, v_moreLinkArgs_1845_);
lean_ctor_set(v_reuseFailAlloc_1860_, 9, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1860_, 10, v_platformIndependent_1848_);
lean_ctor_set(v_reuseFailAlloc_1860_, 11, v_dynlibs_1850_);
lean_ctor_set(v_reuseFailAlloc_1860_, 12, v_plugins_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13, v_buildType_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 1, v_backend_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 2, v_precompileImports_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1852_);
lean_ctor_set_uint8(v_reuseFailAlloc_1860_, sizeof(void*)*13 + 4, v_allowNonModules_1853_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1872_){
_start:
{
uint8_t v_backend_1873_; 
v_backend_1873_ = lean_ctor_get_uint8(v_cfg_1872_, sizeof(void*)*13 + 1);
return v_backend_1873_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1874_){
_start:
{
uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_res_1875_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1874_);
lean_dec_ref(v_cfg_1874_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1877_, lean_object* v_cfg_1878_){
_start:
{
uint8_t v_buildType_1879_; lean_object* v_leanOptions_1880_; lean_object* v_moreLeanArgs_1881_; lean_object* v_weakLeanArgs_1882_; lean_object* v_moreLeancArgs_1883_; lean_object* v_moreServerOptions_1884_; lean_object* v_weakLeancArgs_1885_; lean_object* v_moreLinkObjs_1886_; lean_object* v_moreLinkLibs_1887_; lean_object* v_moreLinkArgs_1888_; lean_object* v_weakLinkArgs_1889_; lean_object* v_platformIndependent_1890_; uint8_t v_precompileImports_1891_; lean_object* v_dynlibs_1892_; lean_object* v_plugins_1893_; uint8_t v_requiresModuleSystem_1894_; uint8_t v_allowNonModules_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_buildType_1879_ = lean_ctor_get_uint8(v_cfg_1878_, sizeof(void*)*13);
v_leanOptions_1880_ = lean_ctor_get(v_cfg_1878_, 0);
v_moreLeanArgs_1881_ = lean_ctor_get(v_cfg_1878_, 1);
v_weakLeanArgs_1882_ = lean_ctor_get(v_cfg_1878_, 2);
v_moreLeancArgs_1883_ = lean_ctor_get(v_cfg_1878_, 3);
v_moreServerOptions_1884_ = lean_ctor_get(v_cfg_1878_, 4);
v_weakLeancArgs_1885_ = lean_ctor_get(v_cfg_1878_, 5);
v_moreLinkObjs_1886_ = lean_ctor_get(v_cfg_1878_, 6);
v_moreLinkLibs_1887_ = lean_ctor_get(v_cfg_1878_, 7);
v_moreLinkArgs_1888_ = lean_ctor_get(v_cfg_1878_, 8);
v_weakLinkArgs_1889_ = lean_ctor_get(v_cfg_1878_, 9);
v_platformIndependent_1890_ = lean_ctor_get(v_cfg_1878_, 10);
v_precompileImports_1891_ = lean_ctor_get_uint8(v_cfg_1878_, sizeof(void*)*13 + 2);
v_dynlibs_1892_ = lean_ctor_get(v_cfg_1878_, 11);
v_plugins_1893_ = lean_ctor_get(v_cfg_1878_, 12);
v_requiresModuleSystem_1894_ = lean_ctor_get_uint8(v_cfg_1878_, sizeof(void*)*13 + 3);
v_allowNonModules_1895_ = lean_ctor_get_uint8(v_cfg_1878_, sizeof(void*)*13 + 4);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_cfg_1878_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v_cfg_1878_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_plugins_1893_);
lean_inc(v_dynlibs_1892_);
lean_inc(v_platformIndependent_1890_);
lean_inc(v_weakLinkArgs_1889_);
lean_inc(v_moreLinkArgs_1888_);
lean_inc(v_moreLinkLibs_1887_);
lean_inc(v_moreLinkObjs_1886_);
lean_inc(v_weakLeancArgs_1885_);
lean_inc(v_moreServerOptions_1884_);
lean_inc(v_moreLeancArgs_1883_);
lean_inc(v_weakLeanArgs_1882_);
lean_inc(v_moreLeanArgs_1881_);
lean_inc(v_leanOptions_1880_);
lean_dec(v_cfg_1878_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_leanOptions_1880_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_moreLeanArgs_1881_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_weakLeanArgs_1882_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_moreLeancArgs_1883_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v_moreServerOptions_1884_);
lean_ctor_set(v_reuseFailAlloc_1901_, 5, v_weakLeancArgs_1885_);
lean_ctor_set(v_reuseFailAlloc_1901_, 6, v_moreLinkObjs_1886_);
lean_ctor_set(v_reuseFailAlloc_1901_, 7, v_moreLinkLibs_1887_);
lean_ctor_set(v_reuseFailAlloc_1901_, 8, v_moreLinkArgs_1888_);
lean_ctor_set(v_reuseFailAlloc_1901_, 9, v_weakLinkArgs_1889_);
lean_ctor_set(v_reuseFailAlloc_1901_, 10, v_platformIndependent_1890_);
lean_ctor_set(v_reuseFailAlloc_1901_, 11, v_dynlibs_1892_);
lean_ctor_set(v_reuseFailAlloc_1901_, 12, v_plugins_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*13, v_buildType_1879_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*13 + 2, v_precompileImports_1891_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*13 + 4, v_allowNonModules_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_ctor_set_uint8(v___x_1900_, sizeof(void*)*13 + 1, v_val_1877_);
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1903_, lean_object* v_cfg_1904_){
_start:
{
uint8_t v_val_88__boxed_1905_; lean_object* v_res_1906_; 
v_val_88__boxed_1905_ = lean_unbox(v_val_1903_);
v_res_1906_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_88__boxed_1905_, v_cfg_1904_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1907_, lean_object* v_cfg_1908_){
_start:
{
uint8_t v_buildType_1909_; lean_object* v_leanOptions_1910_; lean_object* v_moreLeanArgs_1911_; lean_object* v_weakLeanArgs_1912_; lean_object* v_moreLeancArgs_1913_; lean_object* v_moreServerOptions_1914_; lean_object* v_weakLeancArgs_1915_; lean_object* v_moreLinkObjs_1916_; lean_object* v_moreLinkLibs_1917_; lean_object* v_moreLinkArgs_1918_; lean_object* v_weakLinkArgs_1919_; uint8_t v_backend_1920_; lean_object* v_platformIndependent_1921_; uint8_t v_precompileImports_1922_; lean_object* v_dynlibs_1923_; lean_object* v_plugins_1924_; uint8_t v_requiresModuleSystem_1925_; uint8_t v_allowNonModules_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1936_; 
v_buildType_1909_ = lean_ctor_get_uint8(v_cfg_1908_, sizeof(void*)*13);
v_leanOptions_1910_ = lean_ctor_get(v_cfg_1908_, 0);
v_moreLeanArgs_1911_ = lean_ctor_get(v_cfg_1908_, 1);
v_weakLeanArgs_1912_ = lean_ctor_get(v_cfg_1908_, 2);
v_moreLeancArgs_1913_ = lean_ctor_get(v_cfg_1908_, 3);
v_moreServerOptions_1914_ = lean_ctor_get(v_cfg_1908_, 4);
v_weakLeancArgs_1915_ = lean_ctor_get(v_cfg_1908_, 5);
v_moreLinkObjs_1916_ = lean_ctor_get(v_cfg_1908_, 6);
v_moreLinkLibs_1917_ = lean_ctor_get(v_cfg_1908_, 7);
v_moreLinkArgs_1918_ = lean_ctor_get(v_cfg_1908_, 8);
v_weakLinkArgs_1919_ = lean_ctor_get(v_cfg_1908_, 9);
v_backend_1920_ = lean_ctor_get_uint8(v_cfg_1908_, sizeof(void*)*13 + 1);
v_platformIndependent_1921_ = lean_ctor_get(v_cfg_1908_, 10);
v_precompileImports_1922_ = lean_ctor_get_uint8(v_cfg_1908_, sizeof(void*)*13 + 2);
v_dynlibs_1923_ = lean_ctor_get(v_cfg_1908_, 11);
v_plugins_1924_ = lean_ctor_get(v_cfg_1908_, 12);
v_requiresModuleSystem_1925_ = lean_ctor_get_uint8(v_cfg_1908_, sizeof(void*)*13 + 3);
v_allowNonModules_1926_ = lean_ctor_get_uint8(v_cfg_1908_, sizeof(void*)*13 + 4);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_cfg_1908_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1928_ = v_cfg_1908_;
v_isShared_1929_ = v_isSharedCheck_1936_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_plugins_1924_);
lean_inc(v_dynlibs_1923_);
lean_inc(v_platformIndependent_1921_);
lean_inc(v_weakLinkArgs_1919_);
lean_inc(v_moreLinkArgs_1918_);
lean_inc(v_moreLinkLibs_1917_);
lean_inc(v_moreLinkObjs_1916_);
lean_inc(v_weakLeancArgs_1915_);
lean_inc(v_moreServerOptions_1914_);
lean_inc(v_moreLeancArgs_1913_);
lean_inc(v_weakLeanArgs_1912_);
lean_inc(v_moreLeanArgs_1911_);
lean_inc(v_leanOptions_1910_);
lean_dec(v_cfg_1908_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1936_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1930_ = lean_box(v_backend_1920_);
v___x_1931_ = lean_apply_1(v_f_1907_, v___x_1930_);
if (v_isShared_1929_ == 0)
{
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_leanOptions_1910_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_moreLeanArgs_1911_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_weakLeanArgs_1912_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_moreLeancArgs_1913_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_moreServerOptions_1914_);
lean_ctor_set(v_reuseFailAlloc_1935_, 5, v_weakLeancArgs_1915_);
lean_ctor_set(v_reuseFailAlloc_1935_, 6, v_moreLinkObjs_1916_);
lean_ctor_set(v_reuseFailAlloc_1935_, 7, v_moreLinkLibs_1917_);
lean_ctor_set(v_reuseFailAlloc_1935_, 8, v_moreLinkArgs_1918_);
lean_ctor_set(v_reuseFailAlloc_1935_, 9, v_weakLinkArgs_1919_);
lean_ctor_set(v_reuseFailAlloc_1935_, 10, v_platformIndependent_1921_);
lean_ctor_set(v_reuseFailAlloc_1935_, 11, v_dynlibs_1923_);
lean_ctor_set(v_reuseFailAlloc_1935_, 12, v_plugins_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*13, v_buildType_1909_);
v___x_1933_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
uint8_t v___x_1934_; 
v___x_1934_ = lean_unbox(v___x_1931_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*13 + 1, v___x_1934_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*13 + 2, v_precompileImports_1922_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1925_);
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*13 + 4, v_allowNonModules_1926_);
return v___x_1933_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1937_){
_start:
{
uint8_t v___x_1938_; 
v___x_1938_ = 2;
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1939_){
_start:
{
uint8_t v_res_1940_; lean_object* v_r_1941_; 
v_res_1940_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1939_);
lean_dec_ref(v_x_1939_);
v_r_1941_ = lean_box(v_res_1940_);
return v_r_1941_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1953_){
_start:
{
lean_object* v_platformIndependent_1954_; 
v_platformIndependent_1954_ = lean_ctor_get(v_cfg_1953_, 10);
lean_inc(v_platformIndependent_1954_);
return v_platformIndependent_1954_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1955_);
lean_dec_ref(v_cfg_1955_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1957_, lean_object* v_cfg_1958_){
_start:
{
uint8_t v_buildType_1959_; lean_object* v_leanOptions_1960_; lean_object* v_moreLeanArgs_1961_; lean_object* v_weakLeanArgs_1962_; lean_object* v_moreLeancArgs_1963_; lean_object* v_moreServerOptions_1964_; lean_object* v_weakLeancArgs_1965_; lean_object* v_moreLinkObjs_1966_; lean_object* v_moreLinkLibs_1967_; lean_object* v_moreLinkArgs_1968_; lean_object* v_weakLinkArgs_1969_; uint8_t v_backend_1970_; uint8_t v_precompileImports_1971_; lean_object* v_dynlibs_1972_; lean_object* v_plugins_1973_; uint8_t v_requiresModuleSystem_1974_; uint8_t v_allowNonModules_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
v_buildType_1959_ = lean_ctor_get_uint8(v_cfg_1958_, sizeof(void*)*13);
v_leanOptions_1960_ = lean_ctor_get(v_cfg_1958_, 0);
v_moreLeanArgs_1961_ = lean_ctor_get(v_cfg_1958_, 1);
v_weakLeanArgs_1962_ = lean_ctor_get(v_cfg_1958_, 2);
v_moreLeancArgs_1963_ = lean_ctor_get(v_cfg_1958_, 3);
v_moreServerOptions_1964_ = lean_ctor_get(v_cfg_1958_, 4);
v_weakLeancArgs_1965_ = lean_ctor_get(v_cfg_1958_, 5);
v_moreLinkObjs_1966_ = lean_ctor_get(v_cfg_1958_, 6);
v_moreLinkLibs_1967_ = lean_ctor_get(v_cfg_1958_, 7);
v_moreLinkArgs_1968_ = lean_ctor_get(v_cfg_1958_, 8);
v_weakLinkArgs_1969_ = lean_ctor_get(v_cfg_1958_, 9);
v_backend_1970_ = lean_ctor_get_uint8(v_cfg_1958_, sizeof(void*)*13 + 1);
v_precompileImports_1971_ = lean_ctor_get_uint8(v_cfg_1958_, sizeof(void*)*13 + 2);
v_dynlibs_1972_ = lean_ctor_get(v_cfg_1958_, 11);
v_plugins_1973_ = lean_ctor_get(v_cfg_1958_, 12);
v_requiresModuleSystem_1974_ = lean_ctor_get_uint8(v_cfg_1958_, sizeof(void*)*13 + 3);
v_allowNonModules_1975_ = lean_ctor_get_uint8(v_cfg_1958_, sizeof(void*)*13 + 4);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_cfg_1958_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_cfg_1958_, 10);
lean_dec(v_unused_1983_);
v___x_1977_ = v_cfg_1958_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_plugins_1973_);
lean_inc(v_dynlibs_1972_);
lean_inc(v_weakLinkArgs_1969_);
lean_inc(v_moreLinkArgs_1968_);
lean_inc(v_moreLinkLibs_1967_);
lean_inc(v_moreLinkObjs_1966_);
lean_inc(v_weakLeancArgs_1965_);
lean_inc(v_moreServerOptions_1964_);
lean_inc(v_moreLeancArgs_1963_);
lean_inc(v_weakLeanArgs_1962_);
lean_inc(v_moreLeanArgs_1961_);
lean_inc(v_leanOptions_1960_);
lean_dec(v_cfg_1958_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 10, v_val_1957_);
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_leanOptions_1960_);
lean_ctor_set(v_reuseFailAlloc_1981_, 1, v_moreLeanArgs_1961_);
lean_ctor_set(v_reuseFailAlloc_1981_, 2, v_weakLeanArgs_1962_);
lean_ctor_set(v_reuseFailAlloc_1981_, 3, v_moreLeancArgs_1963_);
lean_ctor_set(v_reuseFailAlloc_1981_, 4, v_moreServerOptions_1964_);
lean_ctor_set(v_reuseFailAlloc_1981_, 5, v_weakLeancArgs_1965_);
lean_ctor_set(v_reuseFailAlloc_1981_, 6, v_moreLinkObjs_1966_);
lean_ctor_set(v_reuseFailAlloc_1981_, 7, v_moreLinkLibs_1967_);
lean_ctor_set(v_reuseFailAlloc_1981_, 8, v_moreLinkArgs_1968_);
lean_ctor_set(v_reuseFailAlloc_1981_, 9, v_weakLinkArgs_1969_);
lean_ctor_set(v_reuseFailAlloc_1981_, 10, v_val_1957_);
lean_ctor_set(v_reuseFailAlloc_1981_, 11, v_dynlibs_1972_);
lean_ctor_set(v_reuseFailAlloc_1981_, 12, v_plugins_1973_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*13, v_buildType_1959_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*13 + 1, v_backend_1970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*13 + 2, v_precompileImports_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1981_, sizeof(void*)*13 + 4, v_allowNonModules_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_1984_, lean_object* v_cfg_1985_){
_start:
{
uint8_t v_buildType_1986_; lean_object* v_leanOptions_1987_; lean_object* v_moreLeanArgs_1988_; lean_object* v_weakLeanArgs_1989_; lean_object* v_moreLeancArgs_1990_; lean_object* v_moreServerOptions_1991_; lean_object* v_weakLeancArgs_1992_; lean_object* v_moreLinkObjs_1993_; lean_object* v_moreLinkLibs_1994_; lean_object* v_moreLinkArgs_1995_; lean_object* v_weakLinkArgs_1996_; uint8_t v_backend_1997_; lean_object* v_platformIndependent_1998_; uint8_t v_precompileImports_1999_; lean_object* v_dynlibs_2000_; lean_object* v_plugins_2001_; uint8_t v_requiresModuleSystem_2002_; uint8_t v_allowNonModules_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2011_; 
v_buildType_1986_ = lean_ctor_get_uint8(v_cfg_1985_, sizeof(void*)*13);
v_leanOptions_1987_ = lean_ctor_get(v_cfg_1985_, 0);
v_moreLeanArgs_1988_ = lean_ctor_get(v_cfg_1985_, 1);
v_weakLeanArgs_1989_ = lean_ctor_get(v_cfg_1985_, 2);
v_moreLeancArgs_1990_ = lean_ctor_get(v_cfg_1985_, 3);
v_moreServerOptions_1991_ = lean_ctor_get(v_cfg_1985_, 4);
v_weakLeancArgs_1992_ = lean_ctor_get(v_cfg_1985_, 5);
v_moreLinkObjs_1993_ = lean_ctor_get(v_cfg_1985_, 6);
v_moreLinkLibs_1994_ = lean_ctor_get(v_cfg_1985_, 7);
v_moreLinkArgs_1995_ = lean_ctor_get(v_cfg_1985_, 8);
v_weakLinkArgs_1996_ = lean_ctor_get(v_cfg_1985_, 9);
v_backend_1997_ = lean_ctor_get_uint8(v_cfg_1985_, sizeof(void*)*13 + 1);
v_platformIndependent_1998_ = lean_ctor_get(v_cfg_1985_, 10);
v_precompileImports_1999_ = lean_ctor_get_uint8(v_cfg_1985_, sizeof(void*)*13 + 2);
v_dynlibs_2000_ = lean_ctor_get(v_cfg_1985_, 11);
v_plugins_2001_ = lean_ctor_get(v_cfg_1985_, 12);
v_requiresModuleSystem_2002_ = lean_ctor_get_uint8(v_cfg_1985_, sizeof(void*)*13 + 3);
v_allowNonModules_2003_ = lean_ctor_get_uint8(v_cfg_1985_, sizeof(void*)*13 + 4);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_cfg_1985_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2005_ = v_cfg_1985_;
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_plugins_2001_);
lean_inc(v_dynlibs_2000_);
lean_inc(v_platformIndependent_1998_);
lean_inc(v_weakLinkArgs_1996_);
lean_inc(v_moreLinkArgs_1995_);
lean_inc(v_moreLinkLibs_1994_);
lean_inc(v_moreLinkObjs_1993_);
lean_inc(v_weakLeancArgs_1992_);
lean_inc(v_moreServerOptions_1991_);
lean_inc(v_moreLeancArgs_1990_);
lean_inc(v_weakLeanArgs_1989_);
lean_inc(v_moreLeanArgs_1988_);
lean_inc(v_leanOptions_1987_);
lean_dec(v_cfg_1985_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2011_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_apply_1(v_f_1984_, v_platformIndependent_1998_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 10, v___x_2007_);
v___x_2009_ = v___x_2005_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_leanOptions_1987_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_moreLeanArgs_1988_);
lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_weakLeanArgs_1989_);
lean_ctor_set(v_reuseFailAlloc_2010_, 3, v_moreLeancArgs_1990_);
lean_ctor_set(v_reuseFailAlloc_2010_, 4, v_moreServerOptions_1991_);
lean_ctor_set(v_reuseFailAlloc_2010_, 5, v_weakLeancArgs_1992_);
lean_ctor_set(v_reuseFailAlloc_2010_, 6, v_moreLinkObjs_1993_);
lean_ctor_set(v_reuseFailAlloc_2010_, 7, v_moreLinkLibs_1994_);
lean_ctor_set(v_reuseFailAlloc_2010_, 8, v_moreLinkArgs_1995_);
lean_ctor_set(v_reuseFailAlloc_2010_, 9, v_weakLinkArgs_1996_);
lean_ctor_set(v_reuseFailAlloc_2010_, 10, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2010_, 11, v_dynlibs_2000_);
lean_ctor_set(v_reuseFailAlloc_2010_, 12, v_plugins_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*13, v_buildType_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*13 + 1, v_backend_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*13 + 2, v_precompileImports_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2002_);
lean_ctor_set_uint8(v_reuseFailAlloc_2010_, sizeof(void*)*13 + 4, v_allowNonModules_2003_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_box(0);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_2014_);
lean_dec_ref(v_x_2014_);
return v_res_2015_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__0(lean_object* v_cfg_2027_){
_start:
{
uint8_t v_precompileImports_2028_; 
v_precompileImports_2028_ = lean_ctor_get_uint8(v_cfg_2027_, sizeof(void*)*13 + 2);
return v_precompileImports_2028_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__0___boxed(lean_object* v_cfg_2029_){
_start:
{
uint8_t v_res_2030_; lean_object* v_r_2031_; 
v_res_2030_ = l_Lake_LeanConfig_precompileImports___proj___lam__0(v_cfg_2029_);
lean_dec_ref(v_cfg_2029_);
v_r_2031_ = lean_box(v_res_2030_);
return v_r_2031_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1(uint8_t v_val_2032_, lean_object* v_cfg_2033_){
_start:
{
uint8_t v_buildType_2034_; lean_object* v_leanOptions_2035_; lean_object* v_moreLeanArgs_2036_; lean_object* v_weakLeanArgs_2037_; lean_object* v_moreLeancArgs_2038_; lean_object* v_moreServerOptions_2039_; lean_object* v_weakLeancArgs_2040_; lean_object* v_moreLinkObjs_2041_; lean_object* v_moreLinkLibs_2042_; lean_object* v_moreLinkArgs_2043_; lean_object* v_weakLinkArgs_2044_; uint8_t v_backend_2045_; lean_object* v_platformIndependent_2046_; lean_object* v_dynlibs_2047_; lean_object* v_plugins_2048_; uint8_t v_requiresModuleSystem_2049_; uint8_t v_allowNonModules_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
v_buildType_2034_ = lean_ctor_get_uint8(v_cfg_2033_, sizeof(void*)*13);
v_leanOptions_2035_ = lean_ctor_get(v_cfg_2033_, 0);
v_moreLeanArgs_2036_ = lean_ctor_get(v_cfg_2033_, 1);
v_weakLeanArgs_2037_ = lean_ctor_get(v_cfg_2033_, 2);
v_moreLeancArgs_2038_ = lean_ctor_get(v_cfg_2033_, 3);
v_moreServerOptions_2039_ = lean_ctor_get(v_cfg_2033_, 4);
v_weakLeancArgs_2040_ = lean_ctor_get(v_cfg_2033_, 5);
v_moreLinkObjs_2041_ = lean_ctor_get(v_cfg_2033_, 6);
v_moreLinkLibs_2042_ = lean_ctor_get(v_cfg_2033_, 7);
v_moreLinkArgs_2043_ = lean_ctor_get(v_cfg_2033_, 8);
v_weakLinkArgs_2044_ = lean_ctor_get(v_cfg_2033_, 9);
v_backend_2045_ = lean_ctor_get_uint8(v_cfg_2033_, sizeof(void*)*13 + 1);
v_platformIndependent_2046_ = lean_ctor_get(v_cfg_2033_, 10);
v_dynlibs_2047_ = lean_ctor_get(v_cfg_2033_, 11);
v_plugins_2048_ = lean_ctor_get(v_cfg_2033_, 12);
v_requiresModuleSystem_2049_ = lean_ctor_get_uint8(v_cfg_2033_, sizeof(void*)*13 + 3);
v_allowNonModules_2050_ = lean_ctor_get_uint8(v_cfg_2033_, sizeof(void*)*13 + 4);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_cfg_2033_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v_cfg_2033_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_plugins_2048_);
lean_inc(v_dynlibs_2047_);
lean_inc(v_platformIndependent_2046_);
lean_inc(v_weakLinkArgs_2044_);
lean_inc(v_moreLinkArgs_2043_);
lean_inc(v_moreLinkLibs_2042_);
lean_inc(v_moreLinkObjs_2041_);
lean_inc(v_weakLeancArgs_2040_);
lean_inc(v_moreServerOptions_2039_);
lean_inc(v_moreLeancArgs_2038_);
lean_inc(v_weakLeanArgs_2037_);
lean_inc(v_moreLeanArgs_2036_);
lean_inc(v_leanOptions_2035_);
lean_dec(v_cfg_2033_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_leanOptions_2035_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_moreLeanArgs_2036_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_weakLeanArgs_2037_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_moreLeancArgs_2038_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_moreServerOptions_2039_);
lean_ctor_set(v_reuseFailAlloc_2056_, 5, v_weakLeancArgs_2040_);
lean_ctor_set(v_reuseFailAlloc_2056_, 6, v_moreLinkObjs_2041_);
lean_ctor_set(v_reuseFailAlloc_2056_, 7, v_moreLinkLibs_2042_);
lean_ctor_set(v_reuseFailAlloc_2056_, 8, v_moreLinkArgs_2043_);
lean_ctor_set(v_reuseFailAlloc_2056_, 9, v_weakLinkArgs_2044_);
lean_ctor_set(v_reuseFailAlloc_2056_, 10, v_platformIndependent_2046_);
lean_ctor_set(v_reuseFailAlloc_2056_, 11, v_dynlibs_2047_);
lean_ctor_set(v_reuseFailAlloc_2056_, 12, v_plugins_2048_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*13, v_buildType_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*13 + 1, v_backend_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2056_, sizeof(void*)*13 + 4, v_allowNonModules_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_ctor_set_uint8(v___x_2055_, sizeof(void*)*13 + 2, v_val_2032_);
return v___x_2055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1___boxed(lean_object* v_val_2058_, lean_object* v_cfg_2059_){
_start:
{
uint8_t v_val_88__boxed_2060_; lean_object* v_res_2061_; 
v_val_88__boxed_2060_ = lean_unbox(v_val_2058_);
v_res_2061_ = l_Lake_LeanConfig_precompileImports___proj___lam__1(v_val_88__boxed_2060_, v_cfg_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__2(lean_object* v_f_2062_, lean_object* v_cfg_2063_){
_start:
{
uint8_t v_buildType_2064_; lean_object* v_leanOptions_2065_; lean_object* v_moreLeanArgs_2066_; lean_object* v_weakLeanArgs_2067_; lean_object* v_moreLeancArgs_2068_; lean_object* v_moreServerOptions_2069_; lean_object* v_weakLeancArgs_2070_; lean_object* v_moreLinkObjs_2071_; lean_object* v_moreLinkLibs_2072_; lean_object* v_moreLinkArgs_2073_; lean_object* v_weakLinkArgs_2074_; uint8_t v_backend_2075_; lean_object* v_platformIndependent_2076_; uint8_t v_precompileImports_2077_; lean_object* v_dynlibs_2078_; lean_object* v_plugins_2079_; uint8_t v_requiresModuleSystem_2080_; uint8_t v_allowNonModules_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2091_; 
v_buildType_2064_ = lean_ctor_get_uint8(v_cfg_2063_, sizeof(void*)*13);
v_leanOptions_2065_ = lean_ctor_get(v_cfg_2063_, 0);
v_moreLeanArgs_2066_ = lean_ctor_get(v_cfg_2063_, 1);
v_weakLeanArgs_2067_ = lean_ctor_get(v_cfg_2063_, 2);
v_moreLeancArgs_2068_ = lean_ctor_get(v_cfg_2063_, 3);
v_moreServerOptions_2069_ = lean_ctor_get(v_cfg_2063_, 4);
v_weakLeancArgs_2070_ = lean_ctor_get(v_cfg_2063_, 5);
v_moreLinkObjs_2071_ = lean_ctor_get(v_cfg_2063_, 6);
v_moreLinkLibs_2072_ = lean_ctor_get(v_cfg_2063_, 7);
v_moreLinkArgs_2073_ = lean_ctor_get(v_cfg_2063_, 8);
v_weakLinkArgs_2074_ = lean_ctor_get(v_cfg_2063_, 9);
v_backend_2075_ = lean_ctor_get_uint8(v_cfg_2063_, sizeof(void*)*13 + 1);
v_platformIndependent_2076_ = lean_ctor_get(v_cfg_2063_, 10);
v_precompileImports_2077_ = lean_ctor_get_uint8(v_cfg_2063_, sizeof(void*)*13 + 2);
v_dynlibs_2078_ = lean_ctor_get(v_cfg_2063_, 11);
v_plugins_2079_ = lean_ctor_get(v_cfg_2063_, 12);
v_requiresModuleSystem_2080_ = lean_ctor_get_uint8(v_cfg_2063_, sizeof(void*)*13 + 3);
v_allowNonModules_2081_ = lean_ctor_get_uint8(v_cfg_2063_, sizeof(void*)*13 + 4);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_cfg_2063_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2083_ = v_cfg_2063_;
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_plugins_2079_);
lean_inc(v_dynlibs_2078_);
lean_inc(v_platformIndependent_2076_);
lean_inc(v_weakLinkArgs_2074_);
lean_inc(v_moreLinkArgs_2073_);
lean_inc(v_moreLinkLibs_2072_);
lean_inc(v_moreLinkObjs_2071_);
lean_inc(v_weakLeancArgs_2070_);
lean_inc(v_moreServerOptions_2069_);
lean_inc(v_moreLeancArgs_2068_);
lean_inc(v_weakLeanArgs_2067_);
lean_inc(v_moreLeanArgs_2066_);
lean_inc(v_leanOptions_2065_);
lean_dec(v_cfg_2063_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2091_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2085_ = lean_box(v_precompileImports_2077_);
v___x_2086_ = lean_apply_1(v_f_2062_, v___x_2085_);
if (v_isShared_2084_ == 0)
{
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_leanOptions_2065_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_moreLeanArgs_2066_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_weakLeanArgs_2067_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_moreLeancArgs_2068_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v_moreServerOptions_2069_);
lean_ctor_set(v_reuseFailAlloc_2090_, 5, v_weakLeancArgs_2070_);
lean_ctor_set(v_reuseFailAlloc_2090_, 6, v_moreLinkObjs_2071_);
lean_ctor_set(v_reuseFailAlloc_2090_, 7, v_moreLinkLibs_2072_);
lean_ctor_set(v_reuseFailAlloc_2090_, 8, v_moreLinkArgs_2073_);
lean_ctor_set(v_reuseFailAlloc_2090_, 9, v_weakLinkArgs_2074_);
lean_ctor_set(v_reuseFailAlloc_2090_, 10, v_platformIndependent_2076_);
lean_ctor_set(v_reuseFailAlloc_2090_, 11, v_dynlibs_2078_);
lean_ctor_set(v_reuseFailAlloc_2090_, 12, v_plugins_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*13, v_buildType_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*13 + 1, v_backend_2075_);
v___x_2088_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_unbox(v___x_2086_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*13 + 2, v___x_2089_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2080_);
lean_ctor_set_uint8(v___x_2088_, sizeof(void*)*13 + 4, v_allowNonModules_2081_);
return v___x_2088_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__3(lean_object* v_x_2092_){
_start:
{
uint8_t v___x_2093_; 
v___x_2093_ = 0;
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__3___boxed(lean_object* v_x_2094_){
_start:
{
uint8_t v_res_2095_; lean_object* v_r_2096_; 
v_res_2095_ = l_Lake_LeanConfig_precompileImports___proj___lam__3(v_x_2094_);
lean_dec_ref(v_x_2094_);
v_r_2096_ = lean_box(v_res_2095_);
return v_r_2096_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_2108_){
_start:
{
lean_object* v_dynlibs_2109_; 
v_dynlibs_2109_ = lean_ctor_get(v_cfg_2108_, 11);
lean_inc_ref(v_dynlibs_2109_);
return v_dynlibs_2109_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_2110_);
lean_dec_ref(v_cfg_2110_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_2112_, lean_object* v_cfg_2113_){
_start:
{
uint8_t v_buildType_2114_; lean_object* v_leanOptions_2115_; lean_object* v_moreLeanArgs_2116_; lean_object* v_weakLeanArgs_2117_; lean_object* v_moreLeancArgs_2118_; lean_object* v_moreServerOptions_2119_; lean_object* v_weakLeancArgs_2120_; lean_object* v_moreLinkObjs_2121_; lean_object* v_moreLinkLibs_2122_; lean_object* v_moreLinkArgs_2123_; lean_object* v_weakLinkArgs_2124_; uint8_t v_backend_2125_; lean_object* v_platformIndependent_2126_; uint8_t v_precompileImports_2127_; lean_object* v_plugins_2128_; uint8_t v_requiresModuleSystem_2129_; uint8_t v_allowNonModules_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_buildType_2114_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*13);
v_leanOptions_2115_ = lean_ctor_get(v_cfg_2113_, 0);
v_moreLeanArgs_2116_ = lean_ctor_get(v_cfg_2113_, 1);
v_weakLeanArgs_2117_ = lean_ctor_get(v_cfg_2113_, 2);
v_moreLeancArgs_2118_ = lean_ctor_get(v_cfg_2113_, 3);
v_moreServerOptions_2119_ = lean_ctor_get(v_cfg_2113_, 4);
v_weakLeancArgs_2120_ = lean_ctor_get(v_cfg_2113_, 5);
v_moreLinkObjs_2121_ = lean_ctor_get(v_cfg_2113_, 6);
v_moreLinkLibs_2122_ = lean_ctor_get(v_cfg_2113_, 7);
v_moreLinkArgs_2123_ = lean_ctor_get(v_cfg_2113_, 8);
v_weakLinkArgs_2124_ = lean_ctor_get(v_cfg_2113_, 9);
v_backend_2125_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*13 + 1);
v_platformIndependent_2126_ = lean_ctor_get(v_cfg_2113_, 10);
v_precompileImports_2127_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*13 + 2);
v_plugins_2128_ = lean_ctor_get(v_cfg_2113_, 12);
v_requiresModuleSystem_2129_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*13 + 3);
v_allowNonModules_2130_ = lean_ctor_get_uint8(v_cfg_2113_, sizeof(void*)*13 + 4);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_cfg_2113_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v_cfg_2113_, 11);
lean_dec(v_unused_2138_);
v___x_2132_ = v_cfg_2113_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_plugins_2128_);
lean_inc(v_platformIndependent_2126_);
lean_inc(v_weakLinkArgs_2124_);
lean_inc(v_moreLinkArgs_2123_);
lean_inc(v_moreLinkLibs_2122_);
lean_inc(v_moreLinkObjs_2121_);
lean_inc(v_weakLeancArgs_2120_);
lean_inc(v_moreServerOptions_2119_);
lean_inc(v_moreLeancArgs_2118_);
lean_inc(v_weakLeanArgs_2117_);
lean_inc(v_moreLeanArgs_2116_);
lean_inc(v_leanOptions_2115_);
lean_dec(v_cfg_2113_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 11, v_val_2112_);
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_leanOptions_2115_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_moreLeanArgs_2116_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_weakLeanArgs_2117_);
lean_ctor_set(v_reuseFailAlloc_2136_, 3, v_moreLeancArgs_2118_);
lean_ctor_set(v_reuseFailAlloc_2136_, 4, v_moreServerOptions_2119_);
lean_ctor_set(v_reuseFailAlloc_2136_, 5, v_weakLeancArgs_2120_);
lean_ctor_set(v_reuseFailAlloc_2136_, 6, v_moreLinkObjs_2121_);
lean_ctor_set(v_reuseFailAlloc_2136_, 7, v_moreLinkLibs_2122_);
lean_ctor_set(v_reuseFailAlloc_2136_, 8, v_moreLinkArgs_2123_);
lean_ctor_set(v_reuseFailAlloc_2136_, 9, v_weakLinkArgs_2124_);
lean_ctor_set(v_reuseFailAlloc_2136_, 10, v_platformIndependent_2126_);
lean_ctor_set(v_reuseFailAlloc_2136_, 11, v_val_2112_);
lean_ctor_set(v_reuseFailAlloc_2136_, 12, v_plugins_2128_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*13, v_buildType_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*13 + 1, v_backend_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*13 + 2, v_precompileImports_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2136_, sizeof(void*)*13 + 4, v_allowNonModules_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_2139_, lean_object* v_cfg_2140_){
_start:
{
uint8_t v_buildType_2141_; lean_object* v_leanOptions_2142_; lean_object* v_moreLeanArgs_2143_; lean_object* v_weakLeanArgs_2144_; lean_object* v_moreLeancArgs_2145_; lean_object* v_moreServerOptions_2146_; lean_object* v_weakLeancArgs_2147_; lean_object* v_moreLinkObjs_2148_; lean_object* v_moreLinkLibs_2149_; lean_object* v_moreLinkArgs_2150_; lean_object* v_weakLinkArgs_2151_; uint8_t v_backend_2152_; lean_object* v_platformIndependent_2153_; uint8_t v_precompileImports_2154_; lean_object* v_dynlibs_2155_; lean_object* v_plugins_2156_; uint8_t v_requiresModuleSystem_2157_; uint8_t v_allowNonModules_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2166_; 
v_buildType_2141_ = lean_ctor_get_uint8(v_cfg_2140_, sizeof(void*)*13);
v_leanOptions_2142_ = lean_ctor_get(v_cfg_2140_, 0);
v_moreLeanArgs_2143_ = lean_ctor_get(v_cfg_2140_, 1);
v_weakLeanArgs_2144_ = lean_ctor_get(v_cfg_2140_, 2);
v_moreLeancArgs_2145_ = lean_ctor_get(v_cfg_2140_, 3);
v_moreServerOptions_2146_ = lean_ctor_get(v_cfg_2140_, 4);
v_weakLeancArgs_2147_ = lean_ctor_get(v_cfg_2140_, 5);
v_moreLinkObjs_2148_ = lean_ctor_get(v_cfg_2140_, 6);
v_moreLinkLibs_2149_ = lean_ctor_get(v_cfg_2140_, 7);
v_moreLinkArgs_2150_ = lean_ctor_get(v_cfg_2140_, 8);
v_weakLinkArgs_2151_ = lean_ctor_get(v_cfg_2140_, 9);
v_backend_2152_ = lean_ctor_get_uint8(v_cfg_2140_, sizeof(void*)*13 + 1);
v_platformIndependent_2153_ = lean_ctor_get(v_cfg_2140_, 10);
v_precompileImports_2154_ = lean_ctor_get_uint8(v_cfg_2140_, sizeof(void*)*13 + 2);
v_dynlibs_2155_ = lean_ctor_get(v_cfg_2140_, 11);
v_plugins_2156_ = lean_ctor_get(v_cfg_2140_, 12);
v_requiresModuleSystem_2157_ = lean_ctor_get_uint8(v_cfg_2140_, sizeof(void*)*13 + 3);
v_allowNonModules_2158_ = lean_ctor_get_uint8(v_cfg_2140_, sizeof(void*)*13 + 4);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_cfg_2140_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2160_ = v_cfg_2140_;
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_plugins_2156_);
lean_inc(v_dynlibs_2155_);
lean_inc(v_platformIndependent_2153_);
lean_inc(v_weakLinkArgs_2151_);
lean_inc(v_moreLinkArgs_2150_);
lean_inc(v_moreLinkLibs_2149_);
lean_inc(v_moreLinkObjs_2148_);
lean_inc(v_weakLeancArgs_2147_);
lean_inc(v_moreServerOptions_2146_);
lean_inc(v_moreLeancArgs_2145_);
lean_inc(v_weakLeanArgs_2144_);
lean_inc(v_moreLeanArgs_2143_);
lean_inc(v_leanOptions_2142_);
lean_dec(v_cfg_2140_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2166_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = lean_apply_1(v_f_2139_, v_dynlibs_2155_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 11, v___x_2162_);
v___x_2164_ = v___x_2160_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_leanOptions_2142_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_moreLeanArgs_2143_);
lean_ctor_set(v_reuseFailAlloc_2165_, 2, v_weakLeanArgs_2144_);
lean_ctor_set(v_reuseFailAlloc_2165_, 3, v_moreLeancArgs_2145_);
lean_ctor_set(v_reuseFailAlloc_2165_, 4, v_moreServerOptions_2146_);
lean_ctor_set(v_reuseFailAlloc_2165_, 5, v_weakLeancArgs_2147_);
lean_ctor_set(v_reuseFailAlloc_2165_, 6, v_moreLinkObjs_2148_);
lean_ctor_set(v_reuseFailAlloc_2165_, 7, v_moreLinkLibs_2149_);
lean_ctor_set(v_reuseFailAlloc_2165_, 8, v_moreLinkArgs_2150_);
lean_ctor_set(v_reuseFailAlloc_2165_, 9, v_weakLinkArgs_2151_);
lean_ctor_set(v_reuseFailAlloc_2165_, 10, v_platformIndependent_2153_);
lean_ctor_set(v_reuseFailAlloc_2165_, 11, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2165_, 12, v_plugins_2156_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13, v_buildType_2141_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 1, v_backend_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 2, v_precompileImports_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2157_);
lean_ctor_set_uint8(v_reuseFailAlloc_2165_, sizeof(void*)*13 + 4, v_allowNonModules_2158_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_2177_){
_start:
{
lean_object* v_plugins_2178_; 
v_plugins_2178_ = lean_ctor_get(v_cfg_2177_, 12);
lean_inc_ref(v_plugins_2178_);
return v_plugins_2178_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_2179_);
lean_dec_ref(v_cfg_2179_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_2181_, lean_object* v_cfg_2182_){
_start:
{
uint8_t v_buildType_2183_; lean_object* v_leanOptions_2184_; lean_object* v_moreLeanArgs_2185_; lean_object* v_weakLeanArgs_2186_; lean_object* v_moreLeancArgs_2187_; lean_object* v_moreServerOptions_2188_; lean_object* v_weakLeancArgs_2189_; lean_object* v_moreLinkObjs_2190_; lean_object* v_moreLinkLibs_2191_; lean_object* v_moreLinkArgs_2192_; lean_object* v_weakLinkArgs_2193_; uint8_t v_backend_2194_; lean_object* v_platformIndependent_2195_; uint8_t v_precompileImports_2196_; lean_object* v_dynlibs_2197_; uint8_t v_requiresModuleSystem_2198_; uint8_t v_allowNonModules_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2206_; 
v_buildType_2183_ = lean_ctor_get_uint8(v_cfg_2182_, sizeof(void*)*13);
v_leanOptions_2184_ = lean_ctor_get(v_cfg_2182_, 0);
v_moreLeanArgs_2185_ = lean_ctor_get(v_cfg_2182_, 1);
v_weakLeanArgs_2186_ = lean_ctor_get(v_cfg_2182_, 2);
v_moreLeancArgs_2187_ = lean_ctor_get(v_cfg_2182_, 3);
v_moreServerOptions_2188_ = lean_ctor_get(v_cfg_2182_, 4);
v_weakLeancArgs_2189_ = lean_ctor_get(v_cfg_2182_, 5);
v_moreLinkObjs_2190_ = lean_ctor_get(v_cfg_2182_, 6);
v_moreLinkLibs_2191_ = lean_ctor_get(v_cfg_2182_, 7);
v_moreLinkArgs_2192_ = lean_ctor_get(v_cfg_2182_, 8);
v_weakLinkArgs_2193_ = lean_ctor_get(v_cfg_2182_, 9);
v_backend_2194_ = lean_ctor_get_uint8(v_cfg_2182_, sizeof(void*)*13 + 1);
v_platformIndependent_2195_ = lean_ctor_get(v_cfg_2182_, 10);
v_precompileImports_2196_ = lean_ctor_get_uint8(v_cfg_2182_, sizeof(void*)*13 + 2);
v_dynlibs_2197_ = lean_ctor_get(v_cfg_2182_, 11);
v_requiresModuleSystem_2198_ = lean_ctor_get_uint8(v_cfg_2182_, sizeof(void*)*13 + 3);
v_allowNonModules_2199_ = lean_ctor_get_uint8(v_cfg_2182_, sizeof(void*)*13 + 4);
v_isSharedCheck_2206_ = !lean_is_exclusive(v_cfg_2182_);
if (v_isSharedCheck_2206_ == 0)
{
lean_object* v_unused_2207_; 
v_unused_2207_ = lean_ctor_get(v_cfg_2182_, 12);
lean_dec(v_unused_2207_);
v___x_2201_ = v_cfg_2182_;
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_dynlibs_2197_);
lean_inc(v_platformIndependent_2195_);
lean_inc(v_weakLinkArgs_2193_);
lean_inc(v_moreLinkArgs_2192_);
lean_inc(v_moreLinkLibs_2191_);
lean_inc(v_moreLinkObjs_2190_);
lean_inc(v_weakLeancArgs_2189_);
lean_inc(v_moreServerOptions_2188_);
lean_inc(v_moreLeancArgs_2187_);
lean_inc(v_weakLeanArgs_2186_);
lean_inc(v_moreLeanArgs_2185_);
lean_inc(v_leanOptions_2184_);
lean_dec(v_cfg_2182_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2206_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2204_; 
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 12, v_val_2181_);
v___x_2204_ = v___x_2201_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_leanOptions_2184_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_moreLeanArgs_2185_);
lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_weakLeanArgs_2186_);
lean_ctor_set(v_reuseFailAlloc_2205_, 3, v_moreLeancArgs_2187_);
lean_ctor_set(v_reuseFailAlloc_2205_, 4, v_moreServerOptions_2188_);
lean_ctor_set(v_reuseFailAlloc_2205_, 5, v_weakLeancArgs_2189_);
lean_ctor_set(v_reuseFailAlloc_2205_, 6, v_moreLinkObjs_2190_);
lean_ctor_set(v_reuseFailAlloc_2205_, 7, v_moreLinkLibs_2191_);
lean_ctor_set(v_reuseFailAlloc_2205_, 8, v_moreLinkArgs_2192_);
lean_ctor_set(v_reuseFailAlloc_2205_, 9, v_weakLinkArgs_2193_);
lean_ctor_set(v_reuseFailAlloc_2205_, 10, v_platformIndependent_2195_);
lean_ctor_set(v_reuseFailAlloc_2205_, 11, v_dynlibs_2197_);
lean_ctor_set(v_reuseFailAlloc_2205_, 12, v_val_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*13, v_buildType_2183_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*13 + 1, v_backend_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*13 + 2, v_precompileImports_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2198_);
lean_ctor_set_uint8(v_reuseFailAlloc_2205_, sizeof(void*)*13 + 4, v_allowNonModules_2199_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_2208_, lean_object* v_cfg_2209_){
_start:
{
uint8_t v_buildType_2210_; lean_object* v_leanOptions_2211_; lean_object* v_moreLeanArgs_2212_; lean_object* v_weakLeanArgs_2213_; lean_object* v_moreLeancArgs_2214_; lean_object* v_moreServerOptions_2215_; lean_object* v_weakLeancArgs_2216_; lean_object* v_moreLinkObjs_2217_; lean_object* v_moreLinkLibs_2218_; lean_object* v_moreLinkArgs_2219_; lean_object* v_weakLinkArgs_2220_; uint8_t v_backend_2221_; lean_object* v_platformIndependent_2222_; uint8_t v_precompileImports_2223_; lean_object* v_dynlibs_2224_; lean_object* v_plugins_2225_; uint8_t v_requiresModuleSystem_2226_; uint8_t v_allowNonModules_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2235_; 
v_buildType_2210_ = lean_ctor_get_uint8(v_cfg_2209_, sizeof(void*)*13);
v_leanOptions_2211_ = lean_ctor_get(v_cfg_2209_, 0);
v_moreLeanArgs_2212_ = lean_ctor_get(v_cfg_2209_, 1);
v_weakLeanArgs_2213_ = lean_ctor_get(v_cfg_2209_, 2);
v_moreLeancArgs_2214_ = lean_ctor_get(v_cfg_2209_, 3);
v_moreServerOptions_2215_ = lean_ctor_get(v_cfg_2209_, 4);
v_weakLeancArgs_2216_ = lean_ctor_get(v_cfg_2209_, 5);
v_moreLinkObjs_2217_ = lean_ctor_get(v_cfg_2209_, 6);
v_moreLinkLibs_2218_ = lean_ctor_get(v_cfg_2209_, 7);
v_moreLinkArgs_2219_ = lean_ctor_get(v_cfg_2209_, 8);
v_weakLinkArgs_2220_ = lean_ctor_get(v_cfg_2209_, 9);
v_backend_2221_ = lean_ctor_get_uint8(v_cfg_2209_, sizeof(void*)*13 + 1);
v_platformIndependent_2222_ = lean_ctor_get(v_cfg_2209_, 10);
v_precompileImports_2223_ = lean_ctor_get_uint8(v_cfg_2209_, sizeof(void*)*13 + 2);
v_dynlibs_2224_ = lean_ctor_get(v_cfg_2209_, 11);
v_plugins_2225_ = lean_ctor_get(v_cfg_2209_, 12);
v_requiresModuleSystem_2226_ = lean_ctor_get_uint8(v_cfg_2209_, sizeof(void*)*13 + 3);
v_allowNonModules_2227_ = lean_ctor_get_uint8(v_cfg_2209_, sizeof(void*)*13 + 4);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_cfg_2209_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2229_ = v_cfg_2209_;
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_plugins_2225_);
lean_inc(v_dynlibs_2224_);
lean_inc(v_platformIndependent_2222_);
lean_inc(v_weakLinkArgs_2220_);
lean_inc(v_moreLinkArgs_2219_);
lean_inc(v_moreLinkLibs_2218_);
lean_inc(v_moreLinkObjs_2217_);
lean_inc(v_weakLeancArgs_2216_);
lean_inc(v_moreServerOptions_2215_);
lean_inc(v_moreLeancArgs_2214_);
lean_inc(v_weakLeanArgs_2213_);
lean_inc(v_moreLeanArgs_2212_);
lean_inc(v_leanOptions_2211_);
lean_dec(v_cfg_2209_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2235_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = lean_apply_1(v_f_2208_, v_plugins_2225_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 12, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_leanOptions_2211_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_moreLeanArgs_2212_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_weakLeanArgs_2213_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_moreLeancArgs_2214_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_moreServerOptions_2215_);
lean_ctor_set(v_reuseFailAlloc_2234_, 5, v_weakLeancArgs_2216_);
lean_ctor_set(v_reuseFailAlloc_2234_, 6, v_moreLinkObjs_2217_);
lean_ctor_set(v_reuseFailAlloc_2234_, 7, v_moreLinkLibs_2218_);
lean_ctor_set(v_reuseFailAlloc_2234_, 8, v_moreLinkArgs_2219_);
lean_ctor_set(v_reuseFailAlloc_2234_, 9, v_weakLinkArgs_2220_);
lean_ctor_set(v_reuseFailAlloc_2234_, 10, v_platformIndependent_2222_);
lean_ctor_set(v_reuseFailAlloc_2234_, 11, v_dynlibs_2224_);
lean_ctor_set(v_reuseFailAlloc_2234_, 12, v___x_2231_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*13, v_buildType_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*13 + 1, v_backend_2221_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*13 + 2, v_precompileImports_2223_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2226_);
lean_ctor_set_uint8(v_reuseFailAlloc_2234_, sizeof(void*)*13 + 4, v_allowNonModules_2227_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object* v_cfg_2246_){
_start:
{
uint8_t v_requiresModuleSystem_2247_; 
v_requiresModuleSystem_2247_ = lean_ctor_get_uint8(v_cfg_2246_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_2247_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object* v_cfg_2248_){
_start:
{
uint8_t v_res_2249_; lean_object* v_r_2250_; 
v_res_2249_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2248_);
lean_dec_ref(v_cfg_2248_);
v_r_2250_ = lean_box(v_res_2249_);
return v_r_2250_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t v_val_2251_, lean_object* v_cfg_2252_){
_start:
{
uint8_t v_buildType_2253_; lean_object* v_leanOptions_2254_; lean_object* v_moreLeanArgs_2255_; lean_object* v_weakLeanArgs_2256_; lean_object* v_moreLeancArgs_2257_; lean_object* v_moreServerOptions_2258_; lean_object* v_weakLeancArgs_2259_; lean_object* v_moreLinkObjs_2260_; lean_object* v_moreLinkLibs_2261_; lean_object* v_moreLinkArgs_2262_; lean_object* v_weakLinkArgs_2263_; uint8_t v_backend_2264_; lean_object* v_platformIndependent_2265_; uint8_t v_precompileImports_2266_; lean_object* v_dynlibs_2267_; lean_object* v_plugins_2268_; uint8_t v_allowNonModules_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
v_buildType_2253_ = lean_ctor_get_uint8(v_cfg_2252_, sizeof(void*)*13);
v_leanOptions_2254_ = lean_ctor_get(v_cfg_2252_, 0);
v_moreLeanArgs_2255_ = lean_ctor_get(v_cfg_2252_, 1);
v_weakLeanArgs_2256_ = lean_ctor_get(v_cfg_2252_, 2);
v_moreLeancArgs_2257_ = lean_ctor_get(v_cfg_2252_, 3);
v_moreServerOptions_2258_ = lean_ctor_get(v_cfg_2252_, 4);
v_weakLeancArgs_2259_ = lean_ctor_get(v_cfg_2252_, 5);
v_moreLinkObjs_2260_ = lean_ctor_get(v_cfg_2252_, 6);
v_moreLinkLibs_2261_ = lean_ctor_get(v_cfg_2252_, 7);
v_moreLinkArgs_2262_ = lean_ctor_get(v_cfg_2252_, 8);
v_weakLinkArgs_2263_ = lean_ctor_get(v_cfg_2252_, 9);
v_backend_2264_ = lean_ctor_get_uint8(v_cfg_2252_, sizeof(void*)*13 + 1);
v_platformIndependent_2265_ = lean_ctor_get(v_cfg_2252_, 10);
v_precompileImports_2266_ = lean_ctor_get_uint8(v_cfg_2252_, sizeof(void*)*13 + 2);
v_dynlibs_2267_ = lean_ctor_get(v_cfg_2252_, 11);
v_plugins_2268_ = lean_ctor_get(v_cfg_2252_, 12);
v_allowNonModules_2269_ = lean_ctor_get_uint8(v_cfg_2252_, sizeof(void*)*13 + 4);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_cfg_2252_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v_cfg_2252_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_plugins_2268_);
lean_inc(v_dynlibs_2267_);
lean_inc(v_platformIndependent_2265_);
lean_inc(v_weakLinkArgs_2263_);
lean_inc(v_moreLinkArgs_2262_);
lean_inc(v_moreLinkLibs_2261_);
lean_inc(v_moreLinkObjs_2260_);
lean_inc(v_weakLeancArgs_2259_);
lean_inc(v_moreServerOptions_2258_);
lean_inc(v_moreLeancArgs_2257_);
lean_inc(v_weakLeanArgs_2256_);
lean_inc(v_moreLeanArgs_2255_);
lean_inc(v_leanOptions_2254_);
lean_dec(v_cfg_2252_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_leanOptions_2254_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_moreLeanArgs_2255_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_weakLeanArgs_2256_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_moreLeancArgs_2257_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v_moreServerOptions_2258_);
lean_ctor_set(v_reuseFailAlloc_2275_, 5, v_weakLeancArgs_2259_);
lean_ctor_set(v_reuseFailAlloc_2275_, 6, v_moreLinkObjs_2260_);
lean_ctor_set(v_reuseFailAlloc_2275_, 7, v_moreLinkLibs_2261_);
lean_ctor_set(v_reuseFailAlloc_2275_, 8, v_moreLinkArgs_2262_);
lean_ctor_set(v_reuseFailAlloc_2275_, 9, v_weakLinkArgs_2263_);
lean_ctor_set(v_reuseFailAlloc_2275_, 10, v_platformIndependent_2265_);
lean_ctor_set(v_reuseFailAlloc_2275_, 11, v_dynlibs_2267_);
lean_ctor_set(v_reuseFailAlloc_2275_, 12, v_plugins_2268_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13, v_buildType_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 1, v_backend_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 2, v_precompileImports_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2275_, sizeof(void*)*13 + 4, v_allowNonModules_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_ctor_set_uint8(v___x_2274_, sizeof(void*)*13 + 3, v_val_2251_);
return v___x_2274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object* v_val_2277_, lean_object* v_cfg_2278_){
_start:
{
uint8_t v_val_88__boxed_2279_; lean_object* v_res_2280_; 
v_val_88__boxed_2279_ = lean_unbox(v_val_2277_);
v_res_2280_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_88__boxed_2279_, v_cfg_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object* v_f_2281_, lean_object* v_cfg_2282_){
_start:
{
uint8_t v_buildType_2283_; lean_object* v_leanOptions_2284_; lean_object* v_moreLeanArgs_2285_; lean_object* v_weakLeanArgs_2286_; lean_object* v_moreLeancArgs_2287_; lean_object* v_moreServerOptions_2288_; lean_object* v_weakLeancArgs_2289_; lean_object* v_moreLinkObjs_2290_; lean_object* v_moreLinkLibs_2291_; lean_object* v_moreLinkArgs_2292_; lean_object* v_weakLinkArgs_2293_; uint8_t v_backend_2294_; lean_object* v_platformIndependent_2295_; uint8_t v_precompileImports_2296_; lean_object* v_dynlibs_2297_; lean_object* v_plugins_2298_; uint8_t v_requiresModuleSystem_2299_; uint8_t v_allowNonModules_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2310_; 
v_buildType_2283_ = lean_ctor_get_uint8(v_cfg_2282_, sizeof(void*)*13);
v_leanOptions_2284_ = lean_ctor_get(v_cfg_2282_, 0);
v_moreLeanArgs_2285_ = lean_ctor_get(v_cfg_2282_, 1);
v_weakLeanArgs_2286_ = lean_ctor_get(v_cfg_2282_, 2);
v_moreLeancArgs_2287_ = lean_ctor_get(v_cfg_2282_, 3);
v_moreServerOptions_2288_ = lean_ctor_get(v_cfg_2282_, 4);
v_weakLeancArgs_2289_ = lean_ctor_get(v_cfg_2282_, 5);
v_moreLinkObjs_2290_ = lean_ctor_get(v_cfg_2282_, 6);
v_moreLinkLibs_2291_ = lean_ctor_get(v_cfg_2282_, 7);
v_moreLinkArgs_2292_ = lean_ctor_get(v_cfg_2282_, 8);
v_weakLinkArgs_2293_ = lean_ctor_get(v_cfg_2282_, 9);
v_backend_2294_ = lean_ctor_get_uint8(v_cfg_2282_, sizeof(void*)*13 + 1);
v_platformIndependent_2295_ = lean_ctor_get(v_cfg_2282_, 10);
v_precompileImports_2296_ = lean_ctor_get_uint8(v_cfg_2282_, sizeof(void*)*13 + 2);
v_dynlibs_2297_ = lean_ctor_get(v_cfg_2282_, 11);
v_plugins_2298_ = lean_ctor_get(v_cfg_2282_, 12);
v_requiresModuleSystem_2299_ = lean_ctor_get_uint8(v_cfg_2282_, sizeof(void*)*13 + 3);
v_allowNonModules_2300_ = lean_ctor_get_uint8(v_cfg_2282_, sizeof(void*)*13 + 4);
v_isSharedCheck_2310_ = !lean_is_exclusive(v_cfg_2282_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2302_ = v_cfg_2282_;
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_plugins_2298_);
lean_inc(v_dynlibs_2297_);
lean_inc(v_platformIndependent_2295_);
lean_inc(v_weakLinkArgs_2293_);
lean_inc(v_moreLinkArgs_2292_);
lean_inc(v_moreLinkLibs_2291_);
lean_inc(v_moreLinkObjs_2290_);
lean_inc(v_weakLeancArgs_2289_);
lean_inc(v_moreServerOptions_2288_);
lean_inc(v_moreLeancArgs_2287_);
lean_inc(v_weakLeanArgs_2286_);
lean_inc(v_moreLeanArgs_2285_);
lean_inc(v_leanOptions_2284_);
lean_dec(v_cfg_2282_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2310_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v___x_2304_ = lean_box(v_requiresModuleSystem_2299_);
v___x_2305_ = lean_apply_1(v_f_2281_, v___x_2304_);
if (v_isShared_2303_ == 0)
{
v___x_2307_ = v___x_2302_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_leanOptions_2284_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_moreLeanArgs_2285_);
lean_ctor_set(v_reuseFailAlloc_2309_, 2, v_weakLeanArgs_2286_);
lean_ctor_set(v_reuseFailAlloc_2309_, 3, v_moreLeancArgs_2287_);
lean_ctor_set(v_reuseFailAlloc_2309_, 4, v_moreServerOptions_2288_);
lean_ctor_set(v_reuseFailAlloc_2309_, 5, v_weakLeancArgs_2289_);
lean_ctor_set(v_reuseFailAlloc_2309_, 6, v_moreLinkObjs_2290_);
lean_ctor_set(v_reuseFailAlloc_2309_, 7, v_moreLinkLibs_2291_);
lean_ctor_set(v_reuseFailAlloc_2309_, 8, v_moreLinkArgs_2292_);
lean_ctor_set(v_reuseFailAlloc_2309_, 9, v_weakLinkArgs_2293_);
lean_ctor_set(v_reuseFailAlloc_2309_, 10, v_platformIndependent_2295_);
lean_ctor_set(v_reuseFailAlloc_2309_, 11, v_dynlibs_2297_);
lean_ctor_set(v_reuseFailAlloc_2309_, 12, v_plugins_2298_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*13, v_buildType_2283_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*13 + 1, v_backend_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2309_, sizeof(void*)*13 + 2, v_precompileImports_2296_);
v___x_2307_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_unbox(v___x_2305_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*13 + 3, v___x_2308_);
lean_ctor_set_uint8(v___x_2307_, sizeof(void*)*13 + 4, v_allowNonModules_2300_);
return v___x_2307_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object* v_cfg_2321_){
_start:
{
uint8_t v_allowNonModules_2322_; 
v_allowNonModules_2322_ = lean_ctor_get_uint8(v_cfg_2321_, sizeof(void*)*13 + 4);
return v_allowNonModules_2322_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object* v_cfg_2323_){
_start:
{
uint8_t v_res_2324_; lean_object* v_r_2325_; 
v_res_2324_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2323_);
lean_dec_ref(v_cfg_2323_);
v_r_2325_ = lean_box(v_res_2324_);
return v_r_2325_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t v_val_2326_, lean_object* v_cfg_2327_){
_start:
{
uint8_t v_buildType_2328_; lean_object* v_leanOptions_2329_; lean_object* v_moreLeanArgs_2330_; lean_object* v_weakLeanArgs_2331_; lean_object* v_moreLeancArgs_2332_; lean_object* v_moreServerOptions_2333_; lean_object* v_weakLeancArgs_2334_; lean_object* v_moreLinkObjs_2335_; lean_object* v_moreLinkLibs_2336_; lean_object* v_moreLinkArgs_2337_; lean_object* v_weakLinkArgs_2338_; uint8_t v_backend_2339_; lean_object* v_platformIndependent_2340_; uint8_t v_precompileImports_2341_; lean_object* v_dynlibs_2342_; lean_object* v_plugins_2343_; uint8_t v_requiresModuleSystem_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
v_buildType_2328_ = lean_ctor_get_uint8(v_cfg_2327_, sizeof(void*)*13);
v_leanOptions_2329_ = lean_ctor_get(v_cfg_2327_, 0);
v_moreLeanArgs_2330_ = lean_ctor_get(v_cfg_2327_, 1);
v_weakLeanArgs_2331_ = lean_ctor_get(v_cfg_2327_, 2);
v_moreLeancArgs_2332_ = lean_ctor_get(v_cfg_2327_, 3);
v_moreServerOptions_2333_ = lean_ctor_get(v_cfg_2327_, 4);
v_weakLeancArgs_2334_ = lean_ctor_get(v_cfg_2327_, 5);
v_moreLinkObjs_2335_ = lean_ctor_get(v_cfg_2327_, 6);
v_moreLinkLibs_2336_ = lean_ctor_get(v_cfg_2327_, 7);
v_moreLinkArgs_2337_ = lean_ctor_get(v_cfg_2327_, 8);
v_weakLinkArgs_2338_ = lean_ctor_get(v_cfg_2327_, 9);
v_backend_2339_ = lean_ctor_get_uint8(v_cfg_2327_, sizeof(void*)*13 + 1);
v_platformIndependent_2340_ = lean_ctor_get(v_cfg_2327_, 10);
v_precompileImports_2341_ = lean_ctor_get_uint8(v_cfg_2327_, sizeof(void*)*13 + 2);
v_dynlibs_2342_ = lean_ctor_get(v_cfg_2327_, 11);
v_plugins_2343_ = lean_ctor_get(v_cfg_2327_, 12);
v_requiresModuleSystem_2344_ = lean_ctor_get_uint8(v_cfg_2327_, sizeof(void*)*13 + 3);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_cfg_2327_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v_cfg_2327_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_plugins_2343_);
lean_inc(v_dynlibs_2342_);
lean_inc(v_platformIndependent_2340_);
lean_inc(v_weakLinkArgs_2338_);
lean_inc(v_moreLinkArgs_2337_);
lean_inc(v_moreLinkLibs_2336_);
lean_inc(v_moreLinkObjs_2335_);
lean_inc(v_weakLeancArgs_2334_);
lean_inc(v_moreServerOptions_2333_);
lean_inc(v_moreLeancArgs_2332_);
lean_inc(v_weakLeanArgs_2331_);
lean_inc(v_moreLeanArgs_2330_);
lean_inc(v_leanOptions_2329_);
lean_dec(v_cfg_2327_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_leanOptions_2329_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_moreLeanArgs_2330_);
lean_ctor_set(v_reuseFailAlloc_2350_, 2, v_weakLeanArgs_2331_);
lean_ctor_set(v_reuseFailAlloc_2350_, 3, v_moreLeancArgs_2332_);
lean_ctor_set(v_reuseFailAlloc_2350_, 4, v_moreServerOptions_2333_);
lean_ctor_set(v_reuseFailAlloc_2350_, 5, v_weakLeancArgs_2334_);
lean_ctor_set(v_reuseFailAlloc_2350_, 6, v_moreLinkObjs_2335_);
lean_ctor_set(v_reuseFailAlloc_2350_, 7, v_moreLinkLibs_2336_);
lean_ctor_set(v_reuseFailAlloc_2350_, 8, v_moreLinkArgs_2337_);
lean_ctor_set(v_reuseFailAlloc_2350_, 9, v_weakLinkArgs_2338_);
lean_ctor_set(v_reuseFailAlloc_2350_, 10, v_platformIndependent_2340_);
lean_ctor_set(v_reuseFailAlloc_2350_, 11, v_dynlibs_2342_);
lean_ctor_set(v_reuseFailAlloc_2350_, 12, v_plugins_2343_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*13, v_buildType_2328_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*13 + 1, v_backend_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*13 + 2, v_precompileImports_2341_);
lean_ctor_set_uint8(v_reuseFailAlloc_2350_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_ctor_set_uint8(v___x_2349_, sizeof(void*)*13 + 4, v_val_2326_);
return v___x_2349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object* v_val_2352_, lean_object* v_cfg_2353_){
_start:
{
uint8_t v_val_88__boxed_2354_; lean_object* v_res_2355_; 
v_val_88__boxed_2354_ = lean_unbox(v_val_2352_);
v_res_2355_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_88__boxed_2354_, v_cfg_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object* v_f_2356_, lean_object* v_cfg_2357_){
_start:
{
uint8_t v_buildType_2358_; lean_object* v_leanOptions_2359_; lean_object* v_moreLeanArgs_2360_; lean_object* v_weakLeanArgs_2361_; lean_object* v_moreLeancArgs_2362_; lean_object* v_moreServerOptions_2363_; lean_object* v_weakLeancArgs_2364_; lean_object* v_moreLinkObjs_2365_; lean_object* v_moreLinkLibs_2366_; lean_object* v_moreLinkArgs_2367_; lean_object* v_weakLinkArgs_2368_; uint8_t v_backend_2369_; lean_object* v_platformIndependent_2370_; uint8_t v_precompileImports_2371_; lean_object* v_dynlibs_2372_; lean_object* v_plugins_2373_; uint8_t v_requiresModuleSystem_2374_; uint8_t v_allowNonModules_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2385_; 
v_buildType_2358_ = lean_ctor_get_uint8(v_cfg_2357_, sizeof(void*)*13);
v_leanOptions_2359_ = lean_ctor_get(v_cfg_2357_, 0);
v_moreLeanArgs_2360_ = lean_ctor_get(v_cfg_2357_, 1);
v_weakLeanArgs_2361_ = lean_ctor_get(v_cfg_2357_, 2);
v_moreLeancArgs_2362_ = lean_ctor_get(v_cfg_2357_, 3);
v_moreServerOptions_2363_ = lean_ctor_get(v_cfg_2357_, 4);
v_weakLeancArgs_2364_ = lean_ctor_get(v_cfg_2357_, 5);
v_moreLinkObjs_2365_ = lean_ctor_get(v_cfg_2357_, 6);
v_moreLinkLibs_2366_ = lean_ctor_get(v_cfg_2357_, 7);
v_moreLinkArgs_2367_ = lean_ctor_get(v_cfg_2357_, 8);
v_weakLinkArgs_2368_ = lean_ctor_get(v_cfg_2357_, 9);
v_backend_2369_ = lean_ctor_get_uint8(v_cfg_2357_, sizeof(void*)*13 + 1);
v_platformIndependent_2370_ = lean_ctor_get(v_cfg_2357_, 10);
v_precompileImports_2371_ = lean_ctor_get_uint8(v_cfg_2357_, sizeof(void*)*13 + 2);
v_dynlibs_2372_ = lean_ctor_get(v_cfg_2357_, 11);
v_plugins_2373_ = lean_ctor_get(v_cfg_2357_, 12);
v_requiresModuleSystem_2374_ = lean_ctor_get_uint8(v_cfg_2357_, sizeof(void*)*13 + 3);
v_allowNonModules_2375_ = lean_ctor_get_uint8(v_cfg_2357_, sizeof(void*)*13 + 4);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_cfg_2357_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2377_ = v_cfg_2357_;
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_plugins_2373_);
lean_inc(v_dynlibs_2372_);
lean_inc(v_platformIndependent_2370_);
lean_inc(v_weakLinkArgs_2368_);
lean_inc(v_moreLinkArgs_2367_);
lean_inc(v_moreLinkLibs_2366_);
lean_inc(v_moreLinkObjs_2365_);
lean_inc(v_weakLeancArgs_2364_);
lean_inc(v_moreServerOptions_2363_);
lean_inc(v_moreLeancArgs_2362_);
lean_inc(v_weakLeanArgs_2361_);
lean_inc(v_moreLeanArgs_2360_);
lean_inc(v_leanOptions_2359_);
lean_dec(v_cfg_2357_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2385_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2379_ = lean_box(v_allowNonModules_2375_);
v___x_2380_ = lean_apply_1(v_f_2356_, v___x_2379_);
if (v_isShared_2378_ == 0)
{
v___x_2382_ = v___x_2377_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_leanOptions_2359_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_moreLeanArgs_2360_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_weakLeanArgs_2361_);
lean_ctor_set(v_reuseFailAlloc_2384_, 3, v_moreLeancArgs_2362_);
lean_ctor_set(v_reuseFailAlloc_2384_, 4, v_moreServerOptions_2363_);
lean_ctor_set(v_reuseFailAlloc_2384_, 5, v_weakLeancArgs_2364_);
lean_ctor_set(v_reuseFailAlloc_2384_, 6, v_moreLinkObjs_2365_);
lean_ctor_set(v_reuseFailAlloc_2384_, 7, v_moreLinkLibs_2366_);
lean_ctor_set(v_reuseFailAlloc_2384_, 8, v_moreLinkArgs_2367_);
lean_ctor_set(v_reuseFailAlloc_2384_, 9, v_weakLinkArgs_2368_);
lean_ctor_set(v_reuseFailAlloc_2384_, 10, v_platformIndependent_2370_);
lean_ctor_set(v_reuseFailAlloc_2384_, 11, v_dynlibs_2372_);
lean_ctor_set(v_reuseFailAlloc_2384_, 12, v_plugins_2373_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13, v_buildType_2358_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 1, v_backend_2369_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 2, v_precompileImports_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2384_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2374_);
v___x_2382_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_unbox(v___x_2380_);
lean_ctor_set_uint8(v___x_2382_, sizeof(void*)*13 + 4, v___x_2383_);
return v___x_2382_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2405_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2406_ = lean_array_push(v___x_2405_, v___x_2404_);
return v___x_2406_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2414_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2415_ = lean_array_push(v___x_2414_, v___x_2413_);
return v___x_2415_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2422_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2423_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2424_ = lean_array_push(v___x_2423_, v___x_2422_);
return v___x_2424_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2431_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2432_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2433_ = lean_array_push(v___x_2432_, v___x_2431_);
return v___x_2433_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2440_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2441_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2442_ = lean_array_push(v___x_2441_, v___x_2440_);
return v___x_2442_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2450_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2451_ = lean_array_push(v___x_2450_, v___x_2449_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2459_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2460_ = lean_array_push(v___x_2459_, v___x_2458_);
return v___x_2460_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2468_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2469_ = lean_array_push(v___x_2468_, v___x_2467_);
return v___x_2469_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2477_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2478_ = lean_array_push(v___x_2477_, v___x_2476_);
return v___x_2478_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2486_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2487_ = lean_array_push(v___x_2486_, v___x_2485_);
return v___x_2487_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2495_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2496_ = lean_array_push(v___x_2495_, v___x_2494_);
return v___x_2496_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2504_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2505_ = lean_array_push(v___x_2504_, v___x_2503_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2513_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2514_ = lean_array_push(v___x_2513_, v___x_2512_);
return v___x_2514_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2522_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2523_ = lean_array_push(v___x_2522_, v___x_2521_);
return v___x_2523_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2531_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2532_ = lean_array_push(v___x_2531_, v___x_2530_);
return v___x_2532_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__47));
v___x_2540_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
v___x_2541_ = lean_array_push(v___x_2540_, v___x_2539_);
return v___x_2541_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__51(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__50));
v___x_2549_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__48, &l_Lake_LeanConfig___fields___closed__48_once, _init_l_Lake_LeanConfig___fields___closed__48);
v___x_2550_ = lean_array_push(v___x_2549_, v___x_2548_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__54(void){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__53));
v___x_2558_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__51, &l_Lake_LeanConfig___fields___closed__51_once, _init_l_Lake_LeanConfig___fields___closed__51);
v___x_2559_ = lean_array_push(v___x_2558_, v___x_2557_);
return v___x_2559_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__54, &l_Lake_LeanConfig___fields___closed__54_once, _init_l_Lake_LeanConfig___fields___closed__54);
return v___x_2560_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lake_LeanConfig___fields;
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2562_, lean_object* v_x2_2563_){
_start:
{
lean_object* v_name_2564_; lean_object* v___x_2565_; 
v_name_2564_ = lean_ctor_get(v_x2_2563_, 0);
lean_inc(v_name_2564_);
v___x_2565_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2564_, v_x2_2563_, v_x1_2562_);
return v___x_2565_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
v___x_2566_ = l_Lake_LeanConfig___fields;
v___x_2567_ = lean_array_get_size(v___x_2566_);
return v___x_2567_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2587_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_nat_dec_lt(v___x_2588_, v___x_2587_);
return v___x_2589_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_box(1);
v___x_2592_ = l_Lake_LeanConfig___fields;
v___x_2593_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2592_);
lean_ctor_set(v___x_2593_, 1, v___x_2591_);
lean_ctor_set(v___x_2593_, 2, v___x_2590_);
return v___x_2593_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2595_; uint8_t v___x_2596_; 
v___x_2595_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2596_ = lean_nat_dec_le(v___x_2595_, v___x_2595_);
return v___x_2596_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2597_; size_t v___x_2598_; 
v___x_2597_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2598_ = lean_usize_of_nat(v___x_2597_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2599_; size_t v___x_2600_; size_t v___x_2601_; lean_object* v___x_2602_; lean_object* v___f_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2599_ = lean_box(1);
v___x_2600_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2601_ = ((size_t)0ULL);
v___x_2602_ = l_Lake_LeanConfig___fields;
v___f_2603_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2604_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2604_, v___f_2603_, v___x_2602_, v___x_2601_, v___x_2600_, v___x_2599_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2606_ = lean_unsigned_to_nat(0u);
v___x_2607_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2608_ = l_Lake_LeanConfig___fields;
v___x_2609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2607_);
lean_ctor_set(v___x_2609_, 2, v___x_2606_);
return v___x_2609_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2611_;
}
else
{
uint8_t v___x_2612_; 
v___x_2612_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2612_ == 0)
{
if (v___x_2610_ == 0)
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2613_;
}
else
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2614_;
}
}
else
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2615_;
}
}
}
}
lean_object* runtime_initialize_Lake_Build_Target_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Build_Target_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Backend_instInhabited = _init_l_Lake_Backend_instInhabited();
l_Lake_instInhabitedBuildType_default = _init_l_Lake_instInhabitedBuildType_default();
l_Lake_instInhabitedBuildType = _init_l_Lake_instInhabitedBuildType();
l_Lake_BuildType_instLT = _init_l_Lake_BuildType_instLT();
lean_mark_persistent(l_Lake_BuildType_instLT);
l_Lake_BuildType_instLE = _init_l_Lake_BuildType_instLE();
lean_mark_persistent(l_Lake_BuildType_instLE);
l_Lake_LeanConfig___fields = _init_l_Lake_LeanConfig___fields();
lean_mark_persistent(l_Lake_LeanConfig___fields);
l_Lake_LeanConfig_instConfigFields = _init_l_Lake_LeanConfig_instConfigFields();
lean_mark_persistent(l_Lake_LeanConfig_instConfigFields);
l_Lake_LeanConfig_instConfigInfo = _init_l_Lake_LeanConfig_instConfigInfo();
lean_mark_persistent(l_Lake_LeanConfig_instConfigInfo);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_LeanConfig(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Target_Basic(uint8_t builtin);
lean_object* initialize_Lake_Config_Dynlib(uint8_t builtin);
lean_object* initialize_Lake_Config_MetaClasses(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
lean_object* initialize_Lake_Util_Name(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Lake_Config_Meta(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_LeanConfig(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Target_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Dynlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_MetaClasses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_LeanConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_LeanConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_LeanConfig(builtin);
}
#ifdef __cplusplus
}
#endif

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
lean_object* l_Lake_Backend_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lake_Backend_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lake_Backend_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_Backend_ctorIdx___impl(v_x_4__boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lake_Backend_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
lean_object* l_Lake_Backend_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lake_Backend_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lake_Backend_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lake_Backend_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg(lean_object* v_c_24_){
_start:
{
lean_inc(v_c_24_);
return v_c_24_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg___boxed(lean_object* v_c_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_Backend_c_elim___redArg(v_c_25_);
lean_dec(v_c_25_);
return v_res_26_;
}
}
lean_object* l_Lake_Backend_c_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_c_30_){
_start:
{
lean_inc(v_c_30_);
return v_c_30_;
}
}
LEAN_EXPORT void l_Lake_Backend_c_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_c_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lake_Backend_c_elim(lean_box(0), v_t_28_, lean_box(0), v_c_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_c_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lake_Backend_c_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_c_35_);
lean_dec(v_c_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg(lean_object* v_llvm_38_){
_start:
{
lean_inc(v_llvm_38_);
return v_llvm_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg___boxed(lean_object* v_llvm_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_Backend_llvm_elim___redArg(v_llvm_39_);
lean_dec(v_llvm_39_);
return v_res_40_;
}
}
lean_object* l_Lake_Backend_llvm_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_llvm_44_){
_start:
{
lean_inc(v_llvm_44_);
return v_llvm_44_;
}
}
LEAN_EXPORT void l_Lake_Backend_llvm_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_llvm_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lake_Backend_llvm_elim(lean_box(0), v_t_42_, lean_box(0), v_llvm_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_llvm_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lake_Backend_llvm_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_llvm_49_);
lean_dec(v_llvm_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg(lean_object* v_default_52_){
_start:
{
lean_inc(v_default_52_);
return v_default_52_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg___boxed(lean_object* v_default_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lake_Backend_default_elim___redArg(v_default_53_);
lean_dec(v_default_53_);
return v_res_54_;
}
}
lean_object* l_Lake_Backend_default_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_default_58_){
_start:
{
lean_inc(v_default_58_);
return v_default_58_;
}
}
LEAN_EXPORT void l_Lake_Backend_default_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_default_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lake_Backend_default_elim(lean_box(0), v_t_56_, lean_box(0), v_default_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_default_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lake_Backend_default_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_default_63_);
lean_dec(v_default_63_);
return v_res_65_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__6(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
lean_object* l_Lake_instReprBackend_repr(uint8_t v_x_79_, lean_object* v_prec_80_){
_start:
{
lean_object* v___y_82_; lean_object* v___y_89_; lean_object* v___y_96_; 
switch(v_x_79_)
{
case 0:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_80_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_82_ = v___x_104_;
goto v___jp_81_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_82_ = v___x_105_;
goto v___jp_81_;
}
}
case 1:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_80_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_89_ = v___x_108_;
goto v___jp_88_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_89_ = v___x_109_;
goto v___jp_88_;
}
}
default: 
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = lean_unsigned_to_nat(1024u);
v___x_111_ = lean_nat_dec_le(v___x_110_, v_prec_80_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; 
v___x_112_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_96_ = v___x_112_;
goto v___jp_95_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_96_ = v___x_113_;
goto v___jp_95_;
}
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__1));
lean_inc(v___y_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___y_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = l_Repr_addAppParen(v___x_86_, v_prec_80_);
return v___x_87_;
}
v___jp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_90_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__3));
lean_inc(v___y_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___y_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*1, v___x_92_);
v___x_94_ = l_Repr_addAppParen(v___x_93_, v_prec_80_);
return v___x_94_;
}
v___jp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_97_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__5));
lean_inc(v___y_96_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___y_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
v___x_101_ = l_Repr_addAppParen(v___x_100_, v_prec_80_);
return v___x_101_;
}
}
}
LEAN_EXPORT void l_Lake_instReprBackend_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_79_ = stack[0].m_num;
lean_object* v_prec_80_ = stack[1].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lake_instReprBackend_repr(v_x_79_, v_prec_80_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_171__boxed_117_; lean_object* v_res_118_; 
v_x_171__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lake_instReprBackend_repr(v_x_171__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
uint8_t l_Lake_Backend_ofNat(lean_object* v_n_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_nat_dec_le(v_n_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v___x_125_ = lean_nat_dec_le(v_n_121_, v___x_124_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 2;
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
}
LEAN_EXPORT void l_Lake_Backend_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_121_ = stack[0].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Lake_Backend_ofNat(v_n_121_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofNat___boxed(lean_object* v_n_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lake_Backend_ofNat(v_n_130_);
lean_dec(v_n_130_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
uint8_t l_Lake_instDecidableEqBackend(uint8_t v_x_133_, uint8_t v_y_134_){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_135_ = lean_box(v_x_133_);
v___x_136_ = lean_obj_tag_nat(v___x_135_);
lean_dec(v___x_135_);
v___x_137_ = lean_box(v_y_134_);
v___x_138_ = lean_obj_tag_nat(v___x_137_);
lean_dec(v___x_137_);
v___x_139_ = lean_nat_dec_eq(v___x_136_, v___x_138_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqBackend_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_133_ = stack[0].m_num;
uint8_t v_y_134_ = stack[1].m_num;
uint8_t v_res_140_;
v_res_140_ = l_Lake_instDecidableEqBackend(v_x_133_, v_y_134_);
stack->m_num = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBackend___boxed(lean_object* v_x_141_, lean_object* v_y_142_){
_start:
{
uint8_t v_x_23__boxed_143_; uint8_t v_y_24__boxed_144_; uint8_t v_res_145_; lean_object* v_r_146_; 
v_x_23__boxed_143_ = lean_unbox(v_x_141_);
v_y_24__boxed_144_ = lean_unbox(v_y_142_);
v_res_145_ = l_Lake_instDecidableEqBackend(v_x_23__boxed_143_, v_y_24__boxed_144_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
static uint8_t _init_l_Lake_Backend_instInhabited(void){
_start:
{
uint8_t v___x_147_; 
v___x_147_ = 2;
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f(lean_object* v_s_160_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
v___x_162_ = lean_string_dec_eq(v_s_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
v___x_164_ = lean_string_dec_eq(v_s_160_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
v___x_166_ = lean_string_dec_eq(v_s_160_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__3));
return v___x_168_;
}
}
else
{
lean_object* v___x_169_; 
v___x_169_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__4));
return v___x_169_;
}
}
else
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__5));
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f___boxed(lean_object* v_s_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lake_Backend_ofString_x3f(v_s_171_);
lean_dec_ref(v_s_171_);
return v_res_172_;
}
}
lean_object* l_Lake_Backend_toString(uint8_t v_bt_173_){
_start:
{
switch(v_bt_173_)
{
case 0:
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
return v___x_174_;
}
case 1:
{
lean_object* v___x_175_; 
v___x_175_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
return v___x_175_;
}
default: 
{
lean_object* v___x_176_; 
v___x_176_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
return v___x_176_;
}
}
}
}
LEAN_EXPORT void l_Lake_Backend_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_bt_173_ = stack[0].m_num;
lean_object* v_res_177_;
v_res_177_ = l_Lake_Backend_toString(v_bt_173_);
stack->m_obj
 = v_res_177_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_toString___boxed(lean_object* v_bt_178_){
_start:
{
uint8_t v_bt_boxed_179_; lean_object* v_res_180_; 
v_bt_boxed_179_ = lean_unbox(v_bt_178_);
v_res_180_ = l_Lake_Backend_toString(v_bt_boxed_179_);
return v_res_180_;
}
}
uint8_t l_Lake_Backend_orPreferLeft(uint8_t v_x_183_, uint8_t v_x_184_){
_start:
{
if (v_x_183_ == 2)
{
return v_x_184_;
}
else
{
return v_x_183_;
}
}
}
LEAN_EXPORT void l_Lake_Backend_orPreferLeft_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_183_ = stack[0].m_num;
uint8_t v_x_184_ = stack[1].m_num;
uint8_t v_res_185_;
v_res_185_ = l_Lake_Backend_orPreferLeft(v_x_183_, v_x_184_);
stack->m_num = v_res_185_;
}
LEAN_EXPORT lean_object* l_Lake_Backend_orPreferLeft___boxed(lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
uint8_t v_x_12__boxed_188_; uint8_t v_x_13__boxed_189_; uint8_t v_res_190_; lean_object* v_r_191_; 
v_x_12__boxed_188_ = lean_unbox(v_x_186_);
v_x_13__boxed_189_ = lean_unbox(v_x_187_);
v_res_190_ = l_Lake_Backend_orPreferLeft(v_x_12__boxed_188_, v_x_13__boxed_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
lean_object* l_Lake_BuildType_ctorIdx___impl(uint8_t v_x_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_box(v_x_192_);
v___x_194_ = lean_obj_tag_nat(v___x_193_);
lean_dec(v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT void l_Lake_BuildType_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_192_ = stack[0].m_num;
lean_object* v_res_195_;
v_res_195_ = l_Lake_BuildType_ctorIdx___impl(v_x_192_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___impl___boxed(lean_object* v_x_196_){
_start:
{
uint8_t v_x_4__boxed_197_; lean_object* v_res_198_; 
v_x_4__boxed_197_ = lean_unbox(v_x_196_);
v_res_198_ = l_Lake_BuildType_ctorIdx___impl(v_x_4__boxed_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg(lean_object* v_k_199_){
_start:
{
lean_inc(v_k_199_);
return v_k_199_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg___boxed(lean_object* v_k_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lake_BuildType_ctorElim___redArg(v_k_200_);
lean_dec(v_k_200_);
return v_res_201_;
}
}
lean_object* l_Lake_BuildType_ctorElim(lean_object* v_motive_202_, lean_object* v_ctorIdx_203_, uint8_t v_t_204_, lean_object* v_h_205_, lean_object* v_k_206_){
_start:
{
lean_inc(v_k_206_);
return v_k_206_;
}
}
LEAN_EXPORT void l_Lake_BuildType_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_203_ = stack[1].m_obj;
uint8_t v_t_204_ = stack[2].m_num;
lean_object* v_k_206_ = stack[4].m_obj;
lean_object* v_res_207_;
v_res_207_ = l_Lake_BuildType_ctorElim(lean_box(0), v_ctorIdx_203_, v_t_204_, lean_box(0), v_k_206_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___boxed(lean_object* v_motive_208_, lean_object* v_ctorIdx_209_, lean_object* v_t_210_, lean_object* v_h_211_, lean_object* v_k_212_){
_start:
{
uint8_t v_t_boxed_213_; lean_object* v_res_214_; 
v_t_boxed_213_ = lean_unbox(v_t_210_);
v_res_214_ = l_Lake_BuildType_ctorElim(v_motive_208_, v_ctorIdx_209_, v_t_boxed_213_, v_h_211_, v_k_212_);
lean_dec(v_k_212_);
lean_dec(v_ctorIdx_209_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg(lean_object* v_debug_215_){
_start:
{
lean_inc(v_debug_215_);
return v_debug_215_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg___boxed(lean_object* v_debug_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lake_BuildType_debug_elim___redArg(v_debug_216_);
lean_dec(v_debug_216_);
return v_res_217_;
}
}
lean_object* l_Lake_BuildType_debug_elim(lean_object* v_motive_218_, uint8_t v_t_219_, lean_object* v_h_220_, lean_object* v_debug_221_){
_start:
{
lean_inc(v_debug_221_);
return v_debug_221_;
}
}
LEAN_EXPORT void l_Lake_BuildType_debug_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_219_ = stack[1].m_num;
lean_object* v_debug_221_ = stack[3].m_obj;
lean_object* v_res_222_;
v_res_222_ = l_Lake_BuildType_debug_elim(lean_box(0), v_t_219_, lean_box(0), v_debug_221_);
stack->m_obj
 = v_res_222_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___boxed(lean_object* v_motive_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_debug_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lake_BuildType_debug_elim(v_motive_223_, v_t_boxed_227_, v_h_225_, v_debug_226_);
lean_dec(v_debug_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg(lean_object* v_relWithDebInfo_229_){
_start:
{
lean_inc(v_relWithDebInfo_229_);
return v_relWithDebInfo_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg___boxed(lean_object* v_relWithDebInfo_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lake_BuildType_relWithDebInfo_elim___redArg(v_relWithDebInfo_230_);
lean_dec(v_relWithDebInfo_230_);
return v_res_231_;
}
}
lean_object* l_Lake_BuildType_relWithDebInfo_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_relWithDebInfo_235_){
_start:
{
lean_inc(v_relWithDebInfo_235_);
return v_relWithDebInfo_235_;
}
}
LEAN_EXPORT void l_Lake_BuildType_relWithDebInfo_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_233_ = stack[1].m_num;
lean_object* v_relWithDebInfo_235_ = stack[3].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lake_BuildType_relWithDebInfo_elim(lean_box(0), v_t_233_, lean_box(0), v_relWithDebInfo_235_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_relWithDebInfo_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lake_BuildType_relWithDebInfo_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_relWithDebInfo_240_);
lean_dec(v_relWithDebInfo_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg(lean_object* v_minSizeRel_243_){
_start:
{
lean_inc(v_minSizeRel_243_);
return v_minSizeRel_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg___boxed(lean_object* v_minSizeRel_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_BuildType_minSizeRel_elim___redArg(v_minSizeRel_244_);
lean_dec(v_minSizeRel_244_);
return v_res_245_;
}
}
lean_object* l_Lake_BuildType_minSizeRel_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_minSizeRel_249_){
_start:
{
lean_inc(v_minSizeRel_249_);
return v_minSizeRel_249_;
}
}
LEAN_EXPORT void l_Lake_BuildType_minSizeRel_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_247_ = stack[1].m_num;
lean_object* v_minSizeRel_249_ = stack[3].m_obj;
lean_object* v_res_250_;
v_res_250_ = l_Lake_BuildType_minSizeRel_elim(lean_box(0), v_t_247_, lean_box(0), v_minSizeRel_249_);
stack->m_obj
 = v_res_250_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___boxed(lean_object* v_motive_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_minSizeRel_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Lake_BuildType_minSizeRel_elim(v_motive_251_, v_t_boxed_255_, v_h_253_, v_minSizeRel_254_);
lean_dec(v_minSizeRel_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg(lean_object* v_release_257_){
_start:
{
lean_inc(v_release_257_);
return v_release_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg___boxed(lean_object* v_release_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lake_BuildType_release_elim___redArg(v_release_258_);
lean_dec(v_release_258_);
return v_res_259_;
}
}
lean_object* l_Lake_BuildType_release_elim(lean_object* v_motive_260_, uint8_t v_t_261_, lean_object* v_h_262_, lean_object* v_release_263_){
_start:
{
lean_inc(v_release_263_);
return v_release_263_;
}
}
LEAN_EXPORT void l_Lake_BuildType_release_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_261_ = stack[1].m_num;
lean_object* v_release_263_ = stack[3].m_obj;
lean_object* v_res_264_;
v_res_264_ = l_Lake_BuildType_release_elim(lean_box(0), v_t_261_, lean_box(0), v_release_263_);
stack->m_obj
 = v_res_264_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___boxed(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_release_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Lake_BuildType_release_elim(v_motive_265_, v_t_boxed_269_, v_h_267_, v_release_268_);
lean_dec(v_release_268_);
return v_res_270_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType_default(void){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = 0;
return v___x_271_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType(void){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
lean_object* l_Lake_instReprBuildType_repr(uint8_t v_x_285_, lean_object* v_prec_286_){
_start:
{
lean_object* v___y_288_; lean_object* v___y_295_; lean_object* v___y_302_; lean_object* v___y_309_; 
switch(v_x_285_)
{
case 0:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1024u);
v___x_316_ = lean_nat_dec_le(v___x_315_, v_prec_286_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_288_ = v___x_317_;
goto v___jp_287_;
}
else
{
lean_object* v___x_318_; 
v___x_318_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_288_ = v___x_318_;
goto v___jp_287_;
}
}
case 1:
{
lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(1024u);
v___x_320_ = lean_nat_dec_le(v___x_319_, v_prec_286_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_295_ = v___x_321_;
goto v___jp_294_;
}
else
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_295_ = v___x_322_;
goto v___jp_294_;
}
}
case 2:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(1024u);
v___x_324_ = lean_nat_dec_le(v___x_323_, v_prec_286_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_302_ = v___x_325_;
goto v___jp_301_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_302_ = v___x_326_;
goto v___jp_301_;
}
}
default: 
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = lean_unsigned_to_nat(1024u);
v___x_328_ = lean_nat_dec_le(v___x_327_, v_prec_286_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; 
v___x_329_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_309_ = v___x_329_;
goto v___jp_308_;
}
else
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_309_ = v___x_330_;
goto v___jp_308_;
}
}
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_289_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__1));
lean_inc(v___y_288_);
v___x_290_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_290_, 0, v___y_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = 0;
v___x_292_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*1, v___x_291_);
v___x_293_ = l_Repr_addAppParen(v___x_292_, v_prec_286_);
return v___x_293_;
}
v___jp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_296_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__3));
lean_inc(v___y_295_);
v___x_297_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_297_, 0, v___y_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = 0;
v___x_299_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*1, v___x_298_);
v___x_300_ = l_Repr_addAppParen(v___x_299_, v_prec_286_);
return v___x_300_;
}
v___jp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_303_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__5));
lean_inc(v___y_302_);
v___x_304_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_304_, 0, v___y_302_);
lean_ctor_set(v___x_304_, 1, v___x_303_);
v___x_305_ = 0;
v___x_306_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_306_, 0, v___x_304_);
lean_ctor_set_uint8(v___x_306_, sizeof(void*)*1, v___x_305_);
v___x_307_ = l_Repr_addAppParen(v___x_306_, v_prec_286_);
return v___x_307_;
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_310_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__7));
lean_inc(v___y_309_);
v___x_311_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_311_, 0, v___y_309_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = 0;
v___x_313_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_312_);
v___x_314_ = l_Repr_addAppParen(v___x_313_, v_prec_286_);
return v___x_314_;
}
}
}
LEAN_EXPORT void l_Lake_instReprBuildType_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_285_ = stack[0].m_num;
lean_object* v_prec_286_ = stack[1].m_obj;
lean_object* v_res_331_;
v_res_331_ = l_Lake_instReprBuildType_repr(v_x_285_, v_prec_286_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr___boxed(lean_object* v_x_332_, lean_object* v_prec_333_){
_start:
{
uint8_t v_x_221__boxed_334_; lean_object* v_res_335_; 
v_x_221__boxed_334_ = lean_unbox(v_x_332_);
v_res_335_ = l_Lake_instReprBuildType_repr(v_x_221__boxed_334_, v_prec_333_);
lean_dec(v_prec_333_);
return v_res_335_;
}
}
uint8_t l_Lake_BuildType_ofNat(lean_object* v_n_338_){
_start:
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_dec_le(v_n_338_, v___x_339_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; uint8_t v___x_342_; 
v___x_341_ = lean_unsigned_to_nat(2u);
v___x_342_ = lean_nat_dec_le(v_n_338_, v___x_341_);
if (v___x_342_ == 0)
{
uint8_t v___x_343_; 
v___x_343_ = 3;
return v___x_343_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = 2;
return v___x_344_;
}
}
else
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_nat_dec_le(v_n_338_, v___x_345_);
if (v___x_346_ == 0)
{
uint8_t v___x_347_; 
v___x_347_ = 1;
return v___x_347_;
}
else
{
uint8_t v___x_348_; 
v___x_348_ = 0;
return v___x_348_;
}
}
}
}
LEAN_EXPORT void l_Lake_BuildType_ofNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_338_ = stack[0].m_obj;
uint8_t v_res_349_;
v_res_349_ = l_Lake_BuildType_ofNat(v_n_338_);
stack->m_num = v_res_349_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofNat___boxed(lean_object* v_n_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Lake_BuildType_ofNat(v_n_350_);
lean_dec(v_n_350_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
uint8_t l_Lake_instDecidableEqBuildType(uint8_t v_x_353_, uint8_t v_y_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_355_ = lean_box(v_x_353_);
v___x_356_ = lean_obj_tag_nat(v___x_355_);
lean_dec(v___x_355_);
v___x_357_ = lean_box(v_y_354_);
v___x_358_ = lean_obj_tag_nat(v___x_357_);
lean_dec(v___x_357_);
v___x_359_ = lean_nat_dec_eq(v___x_356_, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT void l_Lake_instDecidableEqBuildType_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_353_ = stack[0].m_num;
uint8_t v_y_354_ = stack[1].m_num;
uint8_t v_res_360_;
v_res_360_ = l_Lake_instDecidableEqBuildType(v_x_353_, v_y_354_);
stack->m_num = v_res_360_;
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildType___boxed(lean_object* v_x_361_, lean_object* v_y_362_){
_start:
{
uint8_t v_x_23__boxed_363_; uint8_t v_y_24__boxed_364_; uint8_t v_res_365_; lean_object* v_r_366_; 
v_x_23__boxed_363_ = lean_unbox(v_x_361_);
v_y_24__boxed_364_ = lean_unbox(v_y_362_);
v_res_365_ = l_Lake_instDecidableEqBuildType(v_x_23__boxed_363_, v_y_24__boxed_364_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
uint8_t l_Lake_instOrdBuildType_ord(uint8_t v_x_367_, uint8_t v_y_368_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_369_ = lean_box(v_x_367_);
v___x_370_ = lean_obj_tag_nat(v___x_369_);
lean_dec(v___x_369_);
v___x_371_ = lean_box(v_y_368_);
v___x_372_ = lean_obj_tag_nat(v___x_371_);
lean_dec(v___x_371_);
v___x_373_ = lean_nat_dec_lt(v___x_370_, v___x_372_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_eq(v___x_370_, v___x_372_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = 2;
return v___x_375_;
}
else
{
uint8_t v___x_376_; 
v___x_376_ = 1;
return v___x_376_;
}
}
else
{
uint8_t v___x_377_; 
v___x_377_ = 0;
return v___x_377_;
}
}
}
LEAN_EXPORT void l_Lake_instOrdBuildType_ord_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_367_ = stack[0].m_num;
uint8_t v_y_368_ = stack[1].m_num;
uint8_t v_res_378_;
v_res_378_ = l_Lake_instOrdBuildType_ord(v_x_367_, v_y_368_);
stack->m_num = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lake_instOrdBuildType_ord___boxed(lean_object* v_x_379_, lean_object* v_y_380_){
_start:
{
uint8_t v_x_33__boxed_381_; uint8_t v_y_34__boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_x_33__boxed_381_ = lean_unbox(v_x_379_);
v_y_34__boxed_382_ = lean_unbox(v_y_380_);
v_res_383_ = l_Lake_instOrdBuildType_ord(v_x_33__boxed_381_, v_y_34__boxed_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
static lean_object* _init_l_Lake_BuildType_instLT(void){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
return v___x_387_;
}
}
static lean_object* _init_l_Lake_BuildType_instLE(void){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = lean_box(0);
return v___x_388_;
}
}
uint8_t l_Lake_BuildType_instMin___lam__0(uint8_t v_x_389_, uint8_t v_y_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = l_Lake_instOrdBuildType_ord(v_x_389_, v_y_390_);
if (v___x_391_ == 2)
{
return v_y_390_;
}
else
{
return v_x_389_;
}
}
}
LEAN_EXPORT void l_Lake_BuildType_instMin___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_389_ = stack[0].m_num;
uint8_t v_y_390_ = stack[1].m_num;
uint8_t v_res_392_;
v_res_392_ = l_Lake_BuildType_instMin___lam__0(v_x_389_, v_y_390_);
stack->m_num = v_res_392_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMin___lam__0___boxed(lean_object* v_x_393_, lean_object* v_y_394_){
_start:
{
uint8_t v_x_boxed_395_; uint8_t v_y_boxed_396_; uint8_t v_res_397_; lean_object* v_r_398_; 
v_x_boxed_395_ = lean_unbox(v_x_393_);
v_y_boxed_396_ = lean_unbox(v_y_394_);
v_res_397_ = l_Lake_BuildType_instMin___lam__0(v_x_boxed_395_, v_y_boxed_396_);
v_r_398_ = lean_box(v_res_397_);
return v_r_398_;
}
}
uint8_t l_Lake_BuildType_instMax___lam__0(uint8_t v_x_401_, uint8_t v_y_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = l_Lake_instOrdBuildType_ord(v_x_401_, v_y_402_);
if (v___x_403_ == 2)
{
return v_x_401_;
}
else
{
return v_y_402_;
}
}
}
LEAN_EXPORT void l_Lake_BuildType_instMax___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_401_ = stack[0].m_num;
uint8_t v_y_402_ = stack[1].m_num;
uint8_t v_res_404_;
v_res_404_ = l_Lake_BuildType_instMax___lam__0(v_x_401_, v_y_402_);
stack->m_num = v_res_404_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMax___lam__0___boxed(lean_object* v_x_405_, lean_object* v_y_406_){
_start:
{
uint8_t v_x_boxed_407_; uint8_t v_y_boxed_408_; uint8_t v_res_409_; lean_object* v_r_410_; 
v_x_boxed_407_ = lean_unbox(v_x_405_);
v_y_boxed_408_ = lean_unbox(v_y_406_);
v_res_409_ = l_Lake_BuildType_instMax___lam__0(v_x_boxed_407_, v_y_boxed_408_);
v_r_410_ = lean_box(v_res_409_);
return v_r_410_;
}
}
lean_object* l_Lake_BuildType_leancArgs(uint8_t v_x_444_){
_start:
{
switch(v_x_444_)
{
case 0:
{
lean_object* v___x_445_; 
v___x_445_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__2));
return v___x_445_;
}
case 1:
{
lean_object* v___x_446_; 
v___x_446_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__5));
return v___x_446_;
}
case 2:
{
lean_object* v___x_447_; 
v___x_447_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__7));
return v___x_447_;
}
default: 
{
lean_object* v___x_448_; 
v___x_448_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__8));
return v___x_448_;
}
}
}
}
LEAN_EXPORT void l_Lake_BuildType_leancArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_444_ = stack[0].m_num;
lean_object* v_res_449_;
v_res_449_ = l_Lake_BuildType_leancArgs(v_x_444_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs___boxed(lean_object* v_x_450_){
_start:
{
uint8_t v_x_163__boxed_451_; lean_object* v_res_452_; 
v_x_163__boxed_451_ = lean_unbox(v_x_450_);
v_res_452_ = l_Lake_BuildType_leancArgs(v_x_163__boxed_451_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofString_x3f(lean_object* v_s_469_){
_start:
{
lean_object* v___y_471_; lean_object* v___x_485_; uint32_t v___x_486_; uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_string_utf8_get(v_s_469_, v___x_485_);
v___x_487_ = 65;
v___x_488_ = lean_uint32_dec_le(v___x_487_, v___x_486_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
v___x_489_ = lean_string_utf8_set(v_s_469_, v___x_485_, v___x_486_);
v___y_471_ = v___x_489_;
goto v___jp_470_;
}
else
{
uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 90;
v___x_491_ = lean_uint32_dec_le(v___x_486_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_string_utf8_set(v_s_469_, v___x_485_, v___x_486_);
v___y_471_ = v___x_492_;
goto v___jp_470_;
}
else
{
uint32_t v___x_493_; uint32_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = 32;
v___x_494_ = lean_uint32_add(v___x_486_, v___x_493_);
v___x_495_ = lean_string_utf8_set(v_s_469_, v___x_485_, v___x_494_);
v___y_471_ = v___x_495_;
goto v___jp_470_;
}
}
v___jp_470_:
{
lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
v___x_473_ = lean_string_dec_eq(v___y_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
v___x_475_ = lean_string_dec_eq(v___y_471_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
v___x_477_ = lean_string_dec_eq(v___y_471_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
v___x_479_ = lean_string_dec_eq(v___y_471_, v___x_478_);
lean_dec_ref(v___y_471_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_box(0);
return v___x_480_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__4));
return v___x_481_;
}
}
else
{
lean_object* v___x_482_; 
lean_dec_ref(v___y_471_);
v___x_482_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__5));
return v___x_482_;
}
}
else
{
lean_object* v___x_483_; 
lean_dec_ref(v___y_471_);
v___x_483_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__6));
return v___x_483_;
}
}
else
{
lean_object* v___x_484_; 
lean_dec_ref(v___y_471_);
v___x_484_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__7));
return v___x_484_;
}
}
}
}
lean_object* l_Lake_BuildType_toString(uint8_t v_bt_496_){
_start:
{
switch(v_bt_496_)
{
case 0:
{
lean_object* v___x_497_; 
v___x_497_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
return v___x_497_;
}
case 1:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
return v___x_498_;
}
case 2:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
return v___x_499_;
}
default: 
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
return v___x_500_;
}
}
}
}
LEAN_EXPORT void l_Lake_BuildType_toString_0interp(lean_interpreter_value* stack)
{
uint8_t v_bt_496_ = stack[0].m_num;
lean_object* v_res_501_;
v_res_501_ = l_Lake_BuildType_toString(v_bt_496_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString___boxed(lean_object* v_bt_502_){
_start:
{
uint8_t v_bt_boxed_503_; lean_object* v_res_504_; 
v_bt_boxed_503_ = lean_unbox(v_bt_502_);
v_res_504_ = l_Lake_BuildType_toString(v_bt_boxed_503_);
return v_res_504_;
}
}
static lean_object* _init_l_Lake_BuildType_leanOptions___closed__3(void){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_512_ = lean_box(1);
v___x_513_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__2));
v___x_514_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__1));
v___x_515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_514_, v___x_513_, v___x_512_);
return v___x_515_;
}
}
lean_object* l_Lake_BuildType_leanOptions(uint8_t v_x_516_){
_start:
{
if (v_x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = lean_obj_once(&l_Lake_BuildType_leanOptions___closed__3, &l_Lake_BuildType_leanOptions___closed__3_once, _init_l_Lake_BuildType_leanOptions___closed__3);
return v___x_517_;
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_box(1);
return v___x_518_;
}
}
}
LEAN_EXPORT void l_Lake_BuildType_leanOptions_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_516_ = stack[0].m_num;
lean_object* v_res_519_;
v_res_519_ = l_Lake_BuildType_leanOptions(v_x_516_);
stack->m_obj
 = v_res_519_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions___boxed(lean_object* v_x_520_){
_start:
{
uint8_t v_x_66__boxed_521_; lean_object* v_res_522_; 
v_x_66__boxed_521_ = lean_unbox(v_x_520_);
v_res_522_ = l_Lake_BuildType_leanOptions(v_x_66__boxed_521_);
return v_res_522_;
}
}
lean_object* l_Lake_BuildType_leanArgs___redArg(){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = ((lean_object*)(l_Lake_BuildType_leanArgs___redArg___closed__0));
return v___x_526_;
}
}
LEAN_EXPORT void l_Lake_BuildType_leanArgs___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_527_;
v_res_527_ = l_Lake_BuildType_leanArgs___redArg();
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___redArg___boxed(lean_object* v___dummy_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lake_BuildType_leanArgs___redArg();
return v_res_529_;
}
}
static lean_object* _init_l_Lake_BuildType_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_530_;
}
}
lean_object* l_Lake_BuildType_leanArgs(uint8_t v_t_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_obj_once(&l_Lake_BuildType_leanArgs___closed__0, &l_Lake_BuildType_leanArgs___closed__0_once, _init_l_Lake_BuildType_leanArgs___closed__0);
return v___x_532_;
}
}
LEAN_EXPORT void l_Lake_BuildType_leanArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_531_ = stack[0].m_num;
lean_object* v_res_533_;
v_res_533_ = l_Lake_BuildType_leanArgs(v_t_531_);
stack->m_obj
 = v_res_533_;
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___boxed(lean_object* v_t_534_){
_start:
{
uint8_t v_t_boxed_535_; lean_object* v_res_536_; 
v_t_boxed_535_ = lean_unbox(v_t_534_);
v_res_536_ = l_Lake_BuildType_leanArgs(v_t_boxed_535_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_object* v___x_555_; 
v___x_555_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1));
return v___x_555_;
}
else
{
lean_object* v_val_556_; lean_object* v___x_557_; uint8_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_val_556_ = lean_ctor_get(v_x_553_, 0);
v___x_557_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3));
v___x_558_ = lean_unbox(v_val_556_);
v___x_559_ = l_Bool_repr___redArg(v___x_558_);
v___x_560_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_557_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Repr_addAppParen(v___x_560_, v_x_554_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_562_, v_x_563_);
lean_dec(v_x_563_);
lean_dec(v_x_562_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object* v_a_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = lean_nat_to_int(v_a_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object* v___y_567_){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = l_String_quote(v___y_567_);
v___x_569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object* v_x_570_, lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_dec(v_x_570_);
return v_x_571_;
}
else
{
lean_object* v_head_573_; lean_object* v_tail_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_585_; 
v_head_573_ = lean_ctor_get(v_x_572_, 0);
v_tail_574_ = lean_ctor_get(v_x_572_, 1);
v_isSharedCheck_585_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_585_ == 0)
{
v___x_576_ = v_x_572_;
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_tail_574_);
lean_inc(v_head_573_);
lean_dec(v_x_572_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_585_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
lean_inc(v_x_570_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 5);
lean_ctor_set(v___x_576_, 1, v_x_570_);
lean_ctor_set(v___x_576_, 0, v_x_571_);
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_x_571_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_x_570_);
v___x_579_ = v_reuseFailAlloc_584_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = l_String_quote(v_head_573_);
v___x_581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
v___x_582_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_579_);
lean_ctor_set(v___x_582_, 1, v___x_581_);
v_x_571_ = v___x_582_;
v_x_572_ = v_tail_574_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_dec(v_x_586_);
return v_x_587_;
}
else
{
lean_object* v_head_589_; lean_object* v_tail_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_601_; 
v_head_589_ = lean_ctor_get(v_x_588_, 0);
v_tail_590_ = lean_ctor_get(v_x_588_, 1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_601_ == 0)
{
v___x_592_ = v_x_588_;
v_isShared_593_ = v_isSharedCheck_601_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_tail_590_);
lean_inc(v_head_589_);
lean_dec(v_x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_601_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
lean_inc(v_x_586_);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 5);
lean_ctor_set(v___x_592_, 1, v_x_586_);
lean_ctor_set(v___x_592_, 0, v_x_587_);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_x_587_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v_x_586_);
v___x_595_ = v_reuseFailAlloc_600_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_596_ = l_String_quote(v_head_589_);
v___x_597_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
v___x_598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_595_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_586_, v___x_598_, v_tail_590_);
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
if (lean_obj_tag(v_x_602_) == 0)
{
lean_object* v___x_604_; 
lean_dec(v_x_603_);
v___x_604_ = lean_box(0);
return v___x_604_;
}
else
{
lean_object* v_tail_605_; 
v_tail_605_ = lean_ctor_get(v_x_602_, 1);
if (lean_obj_tag(v_tail_605_) == 0)
{
lean_object* v_head_606_; lean_object* v___x_607_; 
lean_dec(v_x_603_);
v_head_606_ = lean_ctor_get(v_x_602_, 0);
lean_inc(v_head_606_);
lean_dec_ref_known(v_x_602_, 2);
v___x_607_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_606_);
return v___x_607_;
}
else
{
lean_object* v_head_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_inc(v_tail_605_);
v_head_608_ = lean_ctor_get(v_x_602_, 0);
lean_inc(v_head_608_);
lean_dec_ref_known(v_x_602_, 2);
v___x_609_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_608_);
v___x_610_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_603_, v___x_609_, v_tail_605_);
return v___x_610_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0));
v___x_620_ = lean_string_length(v___x_619_);
return v___x_620_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5);
v___x_622_ = lean_nat_to_int(v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object* v_xs_630_){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = lean_array_get_size(v_xs_630_);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_nat_dec_eq(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_634_ = lean_array_to_list(v_xs_630_);
v___x_635_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_636_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_634_, v___x_635_);
v___x_637_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_638_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_636_);
v___x_640_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_Std_Format_fill(v___x_642_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; 
lean_dec_ref(v_xs_630_);
v___x_644_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object* v___y_645_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = l_Lake_Target_repr___redArg(v___y_645_, v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object* v_x_648_, lean_object* v_x_649_, lean_object* v_x_650_){
_start:
{
if (lean_obj_tag(v_x_650_) == 0)
{
lean_dec(v_x_648_);
return v_x_649_;
}
else
{
lean_object* v_head_651_; lean_object* v_tail_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_663_; 
v_head_651_ = lean_ctor_get(v_x_650_, 0);
v_tail_652_ = lean_ctor_get(v_x_650_, 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_650_);
if (v_isSharedCheck_663_ == 0)
{
v___x_654_ = v_x_650_;
v_isShared_655_ = v_isSharedCheck_663_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_tail_652_);
lean_inc(v_head_651_);
lean_dec(v_x_650_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_663_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
lean_inc(v_x_648_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 5);
lean_ctor_set(v___x_654_, 1, v_x_648_);
lean_ctor_set(v___x_654_, 0, v_x_649_);
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_x_649_);
lean_ctor_set(v_reuseFailAlloc_662_, 1, v_x_648_);
v___x_657_ = v_reuseFailAlloc_662_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l_Lake_Target_repr___redArg(v_head_651_, v___x_658_);
v___x_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_657_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v_x_649_ = v___x_660_;
v_x_650_ = v_tail_652_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_666_) == 0)
{
lean_dec(v_x_664_);
return v_x_665_;
}
else
{
lean_object* v_head_667_; lean_object* v_tail_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_679_; 
v_head_667_ = lean_ctor_get(v_x_666_, 0);
v_tail_668_ = lean_ctor_get(v_x_666_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_x_666_);
if (v_isSharedCheck_679_ == 0)
{
v___x_670_ = v_x_666_;
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_tail_668_);
lean_inc(v_head_667_);
lean_dec(v_x_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_679_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
lean_inc(v_x_664_);
if (v_isShared_671_ == 0)
{
lean_ctor_set_tag(v___x_670_, 5);
lean_ctor_set(v___x_670_, 1, v_x_664_);
lean_ctor_set(v___x_670_, 0, v_x_665_);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_x_665_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v_x_664_);
v___x_673_ = v_reuseFailAlloc_678_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = l_Lake_Target_repr___redArg(v_head_667_, v___x_674_);
v___x_676_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_673_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_664_, v___x_676_, v_tail_668_);
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_680_) == 0)
{
lean_object* v___x_682_; 
lean_dec(v_x_681_);
v___x_682_ = lean_box(0);
return v___x_682_;
}
else
{
lean_object* v_tail_683_; 
v_tail_683_ = lean_ctor_get(v_x_680_, 1);
if (lean_obj_tag(v_tail_683_) == 0)
{
lean_object* v_head_684_; lean_object* v___x_685_; 
lean_dec(v_x_681_);
v_head_684_ = lean_ctor_get(v_x_680_, 0);
lean_inc(v_head_684_);
lean_dec_ref_known(v_x_680_, 2);
v___x_685_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_684_);
return v___x_685_;
}
else
{
lean_object* v_head_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
lean_inc(v_tail_683_);
v_head_686_ = lean_ctor_get(v_x_680_, 0);
lean_inc(v_head_686_);
lean_dec_ref_known(v_x_680_, 2);
v___x_687_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_686_);
v___x_688_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_681_, v___x_687_, v_tail_683_);
return v___x_688_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object* v_xs_689_){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_array_get_size(v_xs_689_);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = lean_nat_dec_eq(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_693_ = lean_array_to_list(v_xs_689_);
v___x_694_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_695_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_693_, v___x_694_);
v___x_696_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_697_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_695_);
v___x_699_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_700_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_698_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
v___x_701_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_696_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_Std_Format_fill(v___x_701_);
return v___x_702_;
}
else
{
lean_object* v___x_703_; 
lean_dec_ref(v_xs_689_);
v___x_703_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 0)
{
lean_dec(v_x_704_);
return v_x_705_;
}
else
{
lean_object* v_head_707_; lean_object* v_tail_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_718_; 
v_head_707_ = lean_ctor_get(v_x_706_, 0);
v_tail_708_ = lean_ctor_get(v_x_706_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_x_706_);
if (v_isSharedCheck_718_ == 0)
{
v___x_710_ = v_x_706_;
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_tail_708_);
lean_inc(v_head_707_);
lean_dec(v_x_706_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
lean_inc(v_x_704_);
if (v_isShared_711_ == 0)
{
lean_ctor_set_tag(v___x_710_, 5);
lean_ctor_set(v___x_710_, 1, v_x_704_);
lean_ctor_set(v___x_710_, 0, v_x_705_);
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_x_705_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_x_704_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = l_Lean_instReprLeanOption_repr___redArg(v_head_707_);
v___x_715_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v_x_705_ = v___x_715_;
v_x_706_ = v_tail_708_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
if (lean_obj_tag(v_x_721_) == 0)
{
lean_dec(v_x_719_);
return v_x_720_;
}
else
{
lean_object* v_head_722_; lean_object* v_tail_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_733_; 
v_head_722_ = lean_ctor_get(v_x_721_, 0);
v_tail_723_ = lean_ctor_get(v_x_721_, 1);
v_isSharedCheck_733_ = !lean_is_exclusive(v_x_721_);
if (v_isSharedCheck_733_ == 0)
{
v___x_725_ = v_x_721_;
v_isShared_726_ = v_isSharedCheck_733_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_tail_723_);
lean_inc(v_head_722_);
lean_dec(v_x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_733_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
lean_inc(v_x_719_);
if (v_isShared_726_ == 0)
{
lean_ctor_set_tag(v___x_725_, 5);
lean_ctor_set(v___x_725_, 1, v_x_719_);
lean_ctor_set(v___x_725_, 0, v_x_720_);
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_x_720_);
lean_ctor_set(v_reuseFailAlloc_732_, 1, v_x_719_);
v___x_728_ = v_reuseFailAlloc_732_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = l_Lean_instReprLeanOption_repr___redArg(v_head_722_);
v___x_730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_728_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_719_, v___x_730_, v_tail_723_);
return v___x_731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_object* v___x_736_; 
lean_dec(v_x_735_);
v___x_736_ = lean_box(0);
return v___x_736_;
}
else
{
lean_object* v_tail_737_; 
v_tail_737_ = lean_ctor_get(v_x_734_, 1);
if (lean_obj_tag(v_tail_737_) == 0)
{
lean_object* v_head_738_; lean_object* v___x_739_; 
lean_dec(v_x_735_);
v_head_738_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_head_738_);
lean_dec_ref_known(v_x_734_, 2);
v___x_739_ = l_Lean_instReprLeanOption_repr___redArg(v_head_738_);
return v___x_739_;
}
else
{
lean_object* v_head_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
lean_inc(v_tail_737_);
v_head_740_ = lean_ctor_get(v_x_734_, 0);
lean_inc(v_head_740_);
lean_dec_ref_known(v_x_734_, 2);
v___x_741_ = l_Lean_instReprLeanOption_repr___redArg(v_head_740_);
v___x_742_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_735_, v___x_741_, v_tail_737_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object* v_xs_743_){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = lean_array_get_size(v_xs_743_);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_nat_dec_eq(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_747_ = lean_array_to_list(v_xs_743_);
v___x_748_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_749_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_747_, v___x_748_);
v___x_750_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_751_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_749_);
v___x_753_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_752_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_750_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
v___x_756_ = l_Std_Format_fill(v___x_755_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; 
lean_dec_ref(v_xs_743_);
v___x_757_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_dec(v_x_758_);
return v_x_759_;
}
else
{
lean_object* v_head_761_; lean_object* v_tail_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_773_; 
v_head_761_ = lean_ctor_get(v_x_760_, 0);
v_tail_762_ = lean_ctor_get(v_x_760_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_x_760_);
if (v_isSharedCheck_773_ == 0)
{
v___x_764_ = v_x_760_;
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_tail_762_);
lean_inc(v_head_761_);
lean_dec(v_x_760_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_773_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
lean_inc(v_x_758_);
if (v_isShared_765_ == 0)
{
lean_ctor_set_tag(v___x_764_, 5);
lean_ctor_set(v___x_764_, 1, v_x_758_);
lean_ctor_set(v___x_764_, 0, v_x_759_);
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_x_759_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_x_758_);
v___x_767_ = v_reuseFailAlloc_772_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = l_Lake_Target_repr___redArg(v_head_761_, v___x_768_);
v___x_770_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_767_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v_x_759_ = v___x_770_;
v_x_760_ = v_tail_762_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_776_) == 0)
{
lean_dec(v_x_774_);
return v_x_775_;
}
else
{
lean_object* v_head_777_; lean_object* v_tail_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v_head_777_ = lean_ctor_get(v_x_776_, 0);
v_tail_778_ = lean_ctor_get(v_x_776_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_x_776_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v_x_776_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_tail_778_);
lean_inc(v_head_777_);
lean_dec(v_x_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
lean_inc(v_x_774_);
if (v_isShared_781_ == 0)
{
lean_ctor_set_tag(v___x_780_, 5);
lean_ctor_set(v___x_780_, 1, v_x_774_);
lean_ctor_set(v___x_780_, 0, v_x_775_);
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_x_775_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_x_774_);
v___x_783_ = v_reuseFailAlloc_788_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = l_Lake_Target_repr___redArg(v_head_777_, v___x_784_);
v___x_786_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_783_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_774_, v___x_786_, v_tail_778_);
return v___x_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
if (lean_obj_tag(v_x_790_) == 0)
{
lean_object* v___x_792_; 
lean_dec(v_x_791_);
v___x_792_ = lean_box(0);
return v___x_792_;
}
else
{
lean_object* v_tail_793_; 
v_tail_793_ = lean_ctor_get(v_x_790_, 1);
if (lean_obj_tag(v_tail_793_) == 0)
{
lean_object* v_head_794_; lean_object* v___x_795_; 
lean_dec(v_x_791_);
v_head_794_ = lean_ctor_get(v_x_790_, 0);
lean_inc(v_head_794_);
lean_dec_ref_known(v_x_790_, 2);
v___x_795_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_794_);
return v___x_795_;
}
else
{
lean_object* v_head_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
lean_inc(v_tail_793_);
v_head_796_ = lean_ctor_get(v_x_790_, 0);
lean_inc(v_head_796_);
lean_dec_ref_known(v_x_790_, 2);
v___x_797_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_796_);
v___x_798_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_791_, v___x_797_, v_tail_793_);
return v___x_798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object* v_xs_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_array_get_size(v_xs_799_);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_nat_dec_eq(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_803_ = lean_array_to_list(v_xs_799_);
v___x_804_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_805_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_803_, v___x_804_);
v___x_806_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_807_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_808_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_805_);
v___x_809_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_810_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_806_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Std_Format_fill(v___x_811_);
return v___x_812_;
}
else
{
lean_object* v___x_813_; 
lean_dec_ref(v_xs_799_);
v___x_813_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_813_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(13u);
v___x_828_ = lean_nat_to_int(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(15u);
v___x_833_ = lean_nat_to_int(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_837_ = lean_unsigned_to_nat(16u);
v___x_838_ = lean_nat_to_int(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(17u);
v___x_846_ = lean_nat_to_int(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(21u);
v___x_851_ = lean_nat_to_int(v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_unsigned_to_nat(11u);
v___x_871_ = lean_nat_to_int(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = lean_unsigned_to_nat(23u);
v___x_876_ = lean_nat_to_int(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = lean_unsigned_to_nat(24u);
v___x_890_ = lean_nat_to_int(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = lean_unsigned_to_nat(19u);
v___x_895_ = lean_nat_to_int(v___x_894_);
return v___x_895_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51(void){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_897_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_898_ = lean_string_length(v___x_897_);
return v___x_898_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__51, &l_Lake_instReprLeanConfig_repr___redArg___closed__51_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51);
v___x_900_ = lean_nat_to_int(v___x_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_905_){
_start:
{
uint8_t v_buildType_906_; lean_object* v_leanOptions_907_; lean_object* v_moreLeanArgs_908_; lean_object* v_weakLeanArgs_909_; lean_object* v_moreLeancArgs_910_; lean_object* v_moreServerOptions_911_; lean_object* v_weakLeancArgs_912_; lean_object* v_moreLinkObjs_913_; lean_object* v_moreLinkLibs_914_; lean_object* v_moreLinkArgs_915_; lean_object* v_weakLinkArgs_916_; uint8_t v_backend_917_; lean_object* v_platformIndependent_918_; uint8_t v_precompileImports_919_; lean_object* v_dynlibs_920_; lean_object* v_plugins_921_; uint8_t v_requiresModuleSystem_922_; uint8_t v_allowNonModules_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_buildType_906_ = lean_ctor_get_uint8(v_x_905_, sizeof(void*)*13);
v_leanOptions_907_ = lean_ctor_get(v_x_905_, 0);
lean_inc_ref(v_leanOptions_907_);
v_moreLeanArgs_908_ = lean_ctor_get(v_x_905_, 1);
lean_inc_ref(v_moreLeanArgs_908_);
v_weakLeanArgs_909_ = lean_ctor_get(v_x_905_, 2);
lean_inc_ref(v_weakLeanArgs_909_);
v_moreLeancArgs_910_ = lean_ctor_get(v_x_905_, 3);
lean_inc_ref(v_moreLeancArgs_910_);
v_moreServerOptions_911_ = lean_ctor_get(v_x_905_, 4);
lean_inc_ref(v_moreServerOptions_911_);
v_weakLeancArgs_912_ = lean_ctor_get(v_x_905_, 5);
lean_inc_ref(v_weakLeancArgs_912_);
v_moreLinkObjs_913_ = lean_ctor_get(v_x_905_, 6);
lean_inc_ref(v_moreLinkObjs_913_);
v_moreLinkLibs_914_ = lean_ctor_get(v_x_905_, 7);
lean_inc_ref(v_moreLinkLibs_914_);
v_moreLinkArgs_915_ = lean_ctor_get(v_x_905_, 8);
lean_inc_ref(v_moreLinkArgs_915_);
v_weakLinkArgs_916_ = lean_ctor_get(v_x_905_, 9);
lean_inc_ref(v_weakLinkArgs_916_);
v_backend_917_ = lean_ctor_get_uint8(v_x_905_, sizeof(void*)*13 + 1);
v_platformIndependent_918_ = lean_ctor_get(v_x_905_, 10);
lean_inc(v_platformIndependent_918_);
v_precompileImports_919_ = lean_ctor_get_uint8(v_x_905_, sizeof(void*)*13 + 2);
v_dynlibs_920_ = lean_ctor_get(v_x_905_, 11);
lean_inc_ref(v_dynlibs_920_);
v_plugins_921_ = lean_ctor_get(v_x_905_, 12);
lean_inc_ref(v_plugins_921_);
v_requiresModuleSystem_922_ = lean_ctor_get_uint8(v_x_905_, sizeof(void*)*13 + 3);
v_allowNonModules_923_ = lean_ctor_get_uint8(v_x_905_, sizeof(void*)*13 + 4);
lean_dec_ref(v_x_905_);
v___x_924_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_925_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_926_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = l_Lake_instReprBuildType_repr(v_buildType_906_, v___x_927_);
v___x_929_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_926_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = 0;
v___x_931_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_931_, 0, v___x_929_);
lean_ctor_set_uint8(v___x_931_, sizeof(void*)*1, v___x_930_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_925_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2));
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_box(1);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__9));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_924_);
v___x_940_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__10, &l_Lake_instReprLeanConfig_repr___redArg___closed__10_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10);
v___x_941_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_907_);
v___x_942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_930_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_933_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_935_);
v___x_947_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__12));
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_924_);
v___x_950_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__13, &l_Lake_instReprLeanConfig_repr___redArg___closed__13_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13);
v___x_951_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_908_);
v___x_952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_930_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_949_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_933_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_935_);
v___x_957_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__15));
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_924_);
v___x_960_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_909_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_950_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_930_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_933_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_935_);
v___x_966_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__17));
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_924_);
v___x_969_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__18, &l_Lake_instReprLeanConfig_repr___redArg___closed__18_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18);
v___x_970_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_910_);
v___x_971_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set_uint8(v___x_972_, sizeof(void*)*1, v___x_930_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_968_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_933_);
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set(v___x_975_, 1, v___x_935_);
v___x_976_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__20));
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_924_);
v___x_979_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__21, &l_Lake_instReprLeanConfig_repr___redArg___closed__21_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21);
v___x_980_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_911_);
v___x_981_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set_uint8(v___x_982_, sizeof(void*)*1, v___x_930_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_978_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_933_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_935_);
v___x_986_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__23));
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_985_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_924_);
v___x_989_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_912_);
v___x_990_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_969_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set_uint8(v___x_991_, sizeof(void*)*1, v___x_930_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_988_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_933_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_935_);
v___x_995_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__25));
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_924_);
v___x_998_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_913_);
v___x_999_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_950_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*1, v___x_930_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_997_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_933_);
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set(v___x_1003_, 1, v___x_935_);
v___x_1004_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__27));
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_924_);
v___x_1007_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_914_);
v___x_1008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_950_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*1, v___x_930_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1006_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_933_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_935_);
v___x_1013_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__29));
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_924_);
v___x_1016_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_915_);
v___x_1017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_950_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*1, v___x_930_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1015_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_933_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_935_);
v___x_1022_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__31));
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_924_);
v___x_1025_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_916_);
v___x_1026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_950_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*1, v___x_930_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_933_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_935_);
v___x_1031_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__33));
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_924_);
v___x_1034_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__34, &l_Lake_instReprLeanConfig_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34);
v___x_1035_ = l_Lake_instReprBackend_repr(v_backend_917_, v___x_927_);
v___x_1036_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*1, v___x_930_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1033_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_933_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_935_);
v___x_1041_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__36));
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_924_);
v___x_1044_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__37, &l_Lake_instReprLeanConfig_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37);
v___x_1045_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_918_, v___x_927_);
lean_dec(v_platformIndependent_918_);
v___x_1046_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*1, v___x_930_);
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1043_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_933_);
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_935_);
v___x_1051_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__39));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_924_);
v___x_1054_ = l_Bool_repr___redArg(v_precompileImports_919_);
v___x_1055_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_979_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*1, v___x_930_);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1053_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_933_);
v___x_1059_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_935_);
v___x_1060_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__41));
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1059_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1061_);
lean_ctor_set(v___x_1062_, 1, v___x_924_);
v___x_1063_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_920_);
v___x_1064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1034_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*1, v___x_930_);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1062_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v___x_933_);
v___x_1068_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___x_935_);
v___x_1069_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__43));
v___x_1070_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v___x_924_);
v___x_1072_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_921_);
v___x_1073_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1034_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set_uint8(v___x_1074_, sizeof(void*)*1, v___x_930_);
v___x_1075_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1071_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_933_);
v___x_1077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___x_935_);
v___x_1078_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__45));
v___x_1079_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
lean_ctor_set(v___x_1080_, 1, v___x_924_);
v___x_1081_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__46, &l_Lake_instReprLeanConfig_repr___redArg___closed__46_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46);
v___x_1082_ = l_Bool_repr___redArg(v_requiresModuleSystem_922_);
v___x_1083_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set_uint8(v___x_1084_, sizeof(void*)*1, v___x_930_);
v___x_1085_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1080_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_933_);
v___x_1087_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v___x_935_);
v___x_1088_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__48));
v___x_1089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v___x_924_);
v___x_1091_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__49, &l_Lake_instReprLeanConfig_repr___redArg___closed__49_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49);
v___x_1092_ = l_Bool_repr___redArg(v_allowNonModules_923_);
v___x_1093_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set_uint8(v___x_1094_, sizeof(void*)*1, v___x_930_);
v___x_1095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1090_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__52, &l_Lake_instReprLeanConfig_repr___redArg___closed__52_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52);
v___x_1097_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__53));
v___x_1098_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___x_1095_);
v___x_1099_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__54));
v___x_1100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1096_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set_uint8(v___x_1102_, sizeof(void*)*1, v___x_930_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1103_, lean_object* v_prec_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1103_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1106_, lean_object* v_prec_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lake_instReprLeanConfig_repr(v_x_1106_, v_prec_1107_);
lean_dec(v_prec_1107_);
return v_res_1108_;
}
}
uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1111_){
_start:
{
uint8_t v_buildType_1112_; 
v_buildType_1112_ = lean_ctor_get_uint8(v_cfg_1111_, sizeof(void*)*13);
return v_buildType_1112_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_buildType___proj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1111_ = stack[0].m_obj;
uint8_t v_res_1113_;
v_res_1113_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1111_);
stack->m_num = v_res_1113_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1114_){
_start:
{
uint8_t v_res_1115_; lean_object* v_r_1116_; 
v_res_1115_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1114_);
lean_dec_ref(v_cfg_1114_);
v_r_1116_ = lean_box(v_res_1115_);
return v_r_1116_;
}
}
lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1117_, lean_object* v_cfg_1118_){
_start:
{
lean_object* v_leanOptions_1119_; lean_object* v_moreLeanArgs_1120_; lean_object* v_weakLeanArgs_1121_; lean_object* v_moreLeancArgs_1122_; lean_object* v_moreServerOptions_1123_; lean_object* v_weakLeancArgs_1124_; lean_object* v_moreLinkObjs_1125_; lean_object* v_moreLinkLibs_1126_; lean_object* v_moreLinkArgs_1127_; lean_object* v_weakLinkArgs_1128_; uint8_t v_backend_1129_; lean_object* v_platformIndependent_1130_; uint8_t v_precompileImports_1131_; lean_object* v_dynlibs_1132_; lean_object* v_plugins_1133_; uint8_t v_requiresModuleSystem_1134_; uint8_t v_allowNonModules_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_leanOptions_1119_ = lean_ctor_get(v_cfg_1118_, 0);
v_moreLeanArgs_1120_ = lean_ctor_get(v_cfg_1118_, 1);
v_weakLeanArgs_1121_ = lean_ctor_get(v_cfg_1118_, 2);
v_moreLeancArgs_1122_ = lean_ctor_get(v_cfg_1118_, 3);
v_moreServerOptions_1123_ = lean_ctor_get(v_cfg_1118_, 4);
v_weakLeancArgs_1124_ = lean_ctor_get(v_cfg_1118_, 5);
v_moreLinkObjs_1125_ = lean_ctor_get(v_cfg_1118_, 6);
v_moreLinkLibs_1126_ = lean_ctor_get(v_cfg_1118_, 7);
v_moreLinkArgs_1127_ = lean_ctor_get(v_cfg_1118_, 8);
v_weakLinkArgs_1128_ = lean_ctor_get(v_cfg_1118_, 9);
v_backend_1129_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 1);
v_platformIndependent_1130_ = lean_ctor_get(v_cfg_1118_, 10);
v_precompileImports_1131_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 2);
v_dynlibs_1132_ = lean_ctor_get(v_cfg_1118_, 11);
v_plugins_1133_ = lean_ctor_get(v_cfg_1118_, 12);
v_requiresModuleSystem_1134_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 3);
v_allowNonModules_1135_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 4);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_cfg_1118_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v_cfg_1118_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_plugins_1133_);
lean_inc(v_dynlibs_1132_);
lean_inc(v_platformIndependent_1130_);
lean_inc(v_weakLinkArgs_1128_);
lean_inc(v_moreLinkArgs_1127_);
lean_inc(v_moreLinkLibs_1126_);
lean_inc(v_moreLinkObjs_1125_);
lean_inc(v_weakLeancArgs_1124_);
lean_inc(v_moreServerOptions_1123_);
lean_inc(v_moreLeancArgs_1122_);
lean_inc(v_weakLeanArgs_1121_);
lean_inc(v_moreLeanArgs_1120_);
lean_inc(v_leanOptions_1119_);
lean_dec(v_cfg_1118_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_leanOptions_1119_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_moreLeanArgs_1120_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_weakLeanArgs_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_moreLeancArgs_1122_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_moreServerOptions_1123_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v_weakLeancArgs_1124_);
lean_ctor_set(v_reuseFailAlloc_1141_, 6, v_moreLinkObjs_1125_);
lean_ctor_set(v_reuseFailAlloc_1141_, 7, v_moreLinkLibs_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 8, v_moreLinkArgs_1127_);
lean_ctor_set(v_reuseFailAlloc_1141_, 9, v_weakLinkArgs_1128_);
lean_ctor_set(v_reuseFailAlloc_1141_, 10, v_platformIndependent_1130_);
lean_ctor_set(v_reuseFailAlloc_1141_, 11, v_dynlibs_1132_);
lean_ctor_set(v_reuseFailAlloc_1141_, 12, v_plugins_1133_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*13 + 1, v_backend_1129_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*13 + 2, v_precompileImports_1131_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1141_, sizeof(void*)*13 + 4, v_allowNonModules_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_ctor_set_uint8(v___x_1140_, sizeof(void*)*13, v_val_1117_);
return v___x_1140_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanConfig_buildType___proj___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_1117_ = stack[0].m_num;
lean_object* v_cfg_1118_ = stack[1].m_obj;
lean_object* v_res_1143_;
v_res_1143_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_1117_, v_cfg_1118_);
stack->m_obj
 = v_res_1143_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1144_, lean_object* v_cfg_1145_){
_start:
{
uint8_t v_val_90__boxed_1146_; lean_object* v_res_1147_; 
v_val_90__boxed_1146_ = lean_unbox(v_val_1144_);
v_res_1147_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_90__boxed_1146_, v_cfg_1145_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1148_, lean_object* v_cfg_1149_){
_start:
{
uint8_t v_buildType_1150_; lean_object* v_leanOptions_1151_; lean_object* v_moreLeanArgs_1152_; lean_object* v_weakLeanArgs_1153_; lean_object* v_moreLeancArgs_1154_; lean_object* v_moreServerOptions_1155_; lean_object* v_weakLeancArgs_1156_; lean_object* v_moreLinkObjs_1157_; lean_object* v_moreLinkLibs_1158_; lean_object* v_moreLinkArgs_1159_; lean_object* v_weakLinkArgs_1160_; uint8_t v_backend_1161_; lean_object* v_platformIndependent_1162_; uint8_t v_precompileImports_1163_; lean_object* v_dynlibs_1164_; lean_object* v_plugins_1165_; uint8_t v_requiresModuleSystem_1166_; uint8_t v_allowNonModules_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1177_; 
v_buildType_1150_ = lean_ctor_get_uint8(v_cfg_1149_, sizeof(void*)*13);
v_leanOptions_1151_ = lean_ctor_get(v_cfg_1149_, 0);
v_moreLeanArgs_1152_ = lean_ctor_get(v_cfg_1149_, 1);
v_weakLeanArgs_1153_ = lean_ctor_get(v_cfg_1149_, 2);
v_moreLeancArgs_1154_ = lean_ctor_get(v_cfg_1149_, 3);
v_moreServerOptions_1155_ = lean_ctor_get(v_cfg_1149_, 4);
v_weakLeancArgs_1156_ = lean_ctor_get(v_cfg_1149_, 5);
v_moreLinkObjs_1157_ = lean_ctor_get(v_cfg_1149_, 6);
v_moreLinkLibs_1158_ = lean_ctor_get(v_cfg_1149_, 7);
v_moreLinkArgs_1159_ = lean_ctor_get(v_cfg_1149_, 8);
v_weakLinkArgs_1160_ = lean_ctor_get(v_cfg_1149_, 9);
v_backend_1161_ = lean_ctor_get_uint8(v_cfg_1149_, sizeof(void*)*13 + 1);
v_platformIndependent_1162_ = lean_ctor_get(v_cfg_1149_, 10);
v_precompileImports_1163_ = lean_ctor_get_uint8(v_cfg_1149_, sizeof(void*)*13 + 2);
v_dynlibs_1164_ = lean_ctor_get(v_cfg_1149_, 11);
v_plugins_1165_ = lean_ctor_get(v_cfg_1149_, 12);
v_requiresModuleSystem_1166_ = lean_ctor_get_uint8(v_cfg_1149_, sizeof(void*)*13 + 3);
v_allowNonModules_1167_ = lean_ctor_get_uint8(v_cfg_1149_, sizeof(void*)*13 + 4);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_cfg_1149_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1169_ = v_cfg_1149_;
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_plugins_1165_);
lean_inc(v_dynlibs_1164_);
lean_inc(v_platformIndependent_1162_);
lean_inc(v_weakLinkArgs_1160_);
lean_inc(v_moreLinkArgs_1159_);
lean_inc(v_moreLinkLibs_1158_);
lean_inc(v_moreLinkObjs_1157_);
lean_inc(v_weakLeancArgs_1156_);
lean_inc(v_moreServerOptions_1155_);
lean_inc(v_moreLeancArgs_1154_);
lean_inc(v_weakLeanArgs_1153_);
lean_inc(v_moreLeanArgs_1152_);
lean_inc(v_leanOptions_1151_);
lean_dec(v_cfg_1149_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1177_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1171_ = lean_box(v_buildType_1150_);
v___x_1172_ = lean_apply_1(v_f_1148_, v___x_1171_);
if (v_isShared_1170_ == 0)
{
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_leanOptions_1151_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v_moreLeanArgs_1152_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_weakLeanArgs_1153_);
lean_ctor_set(v_reuseFailAlloc_1176_, 3, v_moreLeancArgs_1154_);
lean_ctor_set(v_reuseFailAlloc_1176_, 4, v_moreServerOptions_1155_);
lean_ctor_set(v_reuseFailAlloc_1176_, 5, v_weakLeancArgs_1156_);
lean_ctor_set(v_reuseFailAlloc_1176_, 6, v_moreLinkObjs_1157_);
lean_ctor_set(v_reuseFailAlloc_1176_, 7, v_moreLinkLibs_1158_);
lean_ctor_set(v_reuseFailAlloc_1176_, 8, v_moreLinkArgs_1159_);
lean_ctor_set(v_reuseFailAlloc_1176_, 9, v_weakLinkArgs_1160_);
lean_ctor_set(v_reuseFailAlloc_1176_, 10, v_platformIndependent_1162_);
lean_ctor_set(v_reuseFailAlloc_1176_, 11, v_dynlibs_1164_);
lean_ctor_set(v_reuseFailAlloc_1176_, 12, v_plugins_1165_);
v___x_1174_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_unbox(v___x_1172_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*13, v___x_1175_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*13 + 1, v_backend_1161_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*13 + 2, v_precompileImports_1163_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1166_);
lean_ctor_set_uint8(v___x_1174_, sizeof(void*)*13 + 4, v_allowNonModules_1167_);
return v___x_1174_;
}
}
}
}
uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1178_){
_start:
{
uint8_t v___x_1179_; 
v___x_1179_ = 3;
return v___x_1179_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_buildType___proj___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1178_ = stack[0].m_obj;
uint8_t v_res_1180_;
v_res_1180_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1178_);
stack->m_num = v_res_1180_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1181_);
lean_dec_ref(v_x_1181_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1195_){
_start:
{
lean_object* v_leanOptions_1196_; 
v_leanOptions_1196_ = lean_ctor_get(v_cfg_1195_, 0);
lean_inc_ref(v_leanOptions_1196_);
return v_leanOptions_1196_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1197_);
lean_dec_ref(v_cfg_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1199_, lean_object* v_cfg_1200_){
_start:
{
uint8_t v_buildType_1201_; lean_object* v_moreLeanArgs_1202_; lean_object* v_weakLeanArgs_1203_; lean_object* v_moreLeancArgs_1204_; lean_object* v_moreServerOptions_1205_; lean_object* v_weakLeancArgs_1206_; lean_object* v_moreLinkObjs_1207_; lean_object* v_moreLinkLibs_1208_; lean_object* v_moreLinkArgs_1209_; lean_object* v_weakLinkArgs_1210_; uint8_t v_backend_1211_; lean_object* v_platformIndependent_1212_; uint8_t v_precompileImports_1213_; lean_object* v_dynlibs_1214_; lean_object* v_plugins_1215_; uint8_t v_requiresModuleSystem_1216_; uint8_t v_allowNonModules_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_buildType_1201_ = lean_ctor_get_uint8(v_cfg_1200_, sizeof(void*)*13);
v_moreLeanArgs_1202_ = lean_ctor_get(v_cfg_1200_, 1);
v_weakLeanArgs_1203_ = lean_ctor_get(v_cfg_1200_, 2);
v_moreLeancArgs_1204_ = lean_ctor_get(v_cfg_1200_, 3);
v_moreServerOptions_1205_ = lean_ctor_get(v_cfg_1200_, 4);
v_weakLeancArgs_1206_ = lean_ctor_get(v_cfg_1200_, 5);
v_moreLinkObjs_1207_ = lean_ctor_get(v_cfg_1200_, 6);
v_moreLinkLibs_1208_ = lean_ctor_get(v_cfg_1200_, 7);
v_moreLinkArgs_1209_ = lean_ctor_get(v_cfg_1200_, 8);
v_weakLinkArgs_1210_ = lean_ctor_get(v_cfg_1200_, 9);
v_backend_1211_ = lean_ctor_get_uint8(v_cfg_1200_, sizeof(void*)*13 + 1);
v_platformIndependent_1212_ = lean_ctor_get(v_cfg_1200_, 10);
v_precompileImports_1213_ = lean_ctor_get_uint8(v_cfg_1200_, sizeof(void*)*13 + 2);
v_dynlibs_1214_ = lean_ctor_get(v_cfg_1200_, 11);
v_plugins_1215_ = lean_ctor_get(v_cfg_1200_, 12);
v_requiresModuleSystem_1216_ = lean_ctor_get_uint8(v_cfg_1200_, sizeof(void*)*13 + 3);
v_allowNonModules_1217_ = lean_ctor_get_uint8(v_cfg_1200_, sizeof(void*)*13 + 4);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_cfg_1200_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v_cfg_1200_, 0);
lean_dec(v_unused_1225_);
v___x_1219_ = v_cfg_1200_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_plugins_1215_);
lean_inc(v_dynlibs_1214_);
lean_inc(v_platformIndependent_1212_);
lean_inc(v_weakLinkArgs_1210_);
lean_inc(v_moreLinkArgs_1209_);
lean_inc(v_moreLinkLibs_1208_);
lean_inc(v_moreLinkObjs_1207_);
lean_inc(v_weakLeancArgs_1206_);
lean_inc(v_moreServerOptions_1205_);
lean_inc(v_moreLeancArgs_1204_);
lean_inc(v_weakLeanArgs_1203_);
lean_inc(v_moreLeanArgs_1202_);
lean_dec(v_cfg_1200_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v_val_1199_);
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_val_1199_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_moreLeanArgs_1202_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_weakLeanArgs_1203_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_moreLeancArgs_1204_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_moreServerOptions_1205_);
lean_ctor_set(v_reuseFailAlloc_1223_, 5, v_weakLeancArgs_1206_);
lean_ctor_set(v_reuseFailAlloc_1223_, 6, v_moreLinkObjs_1207_);
lean_ctor_set(v_reuseFailAlloc_1223_, 7, v_moreLinkLibs_1208_);
lean_ctor_set(v_reuseFailAlloc_1223_, 8, v_moreLinkArgs_1209_);
lean_ctor_set(v_reuseFailAlloc_1223_, 9, v_weakLinkArgs_1210_);
lean_ctor_set(v_reuseFailAlloc_1223_, 10, v_platformIndependent_1212_);
lean_ctor_set(v_reuseFailAlloc_1223_, 11, v_dynlibs_1214_);
lean_ctor_set(v_reuseFailAlloc_1223_, 12, v_plugins_1215_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*13, v_buildType_1201_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*13 + 1, v_backend_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*13 + 2, v_precompileImports_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1216_);
lean_ctor_set_uint8(v_reuseFailAlloc_1223_, sizeof(void*)*13 + 4, v_allowNonModules_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1226_, lean_object* v_cfg_1227_){
_start:
{
uint8_t v_buildType_1228_; lean_object* v_leanOptions_1229_; lean_object* v_moreLeanArgs_1230_; lean_object* v_weakLeanArgs_1231_; lean_object* v_moreLeancArgs_1232_; lean_object* v_moreServerOptions_1233_; lean_object* v_weakLeancArgs_1234_; lean_object* v_moreLinkObjs_1235_; lean_object* v_moreLinkLibs_1236_; lean_object* v_moreLinkArgs_1237_; lean_object* v_weakLinkArgs_1238_; uint8_t v_backend_1239_; lean_object* v_platformIndependent_1240_; uint8_t v_precompileImports_1241_; lean_object* v_dynlibs_1242_; lean_object* v_plugins_1243_; uint8_t v_requiresModuleSystem_1244_; uint8_t v_allowNonModules_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1253_; 
v_buildType_1228_ = lean_ctor_get_uint8(v_cfg_1227_, sizeof(void*)*13);
v_leanOptions_1229_ = lean_ctor_get(v_cfg_1227_, 0);
v_moreLeanArgs_1230_ = lean_ctor_get(v_cfg_1227_, 1);
v_weakLeanArgs_1231_ = lean_ctor_get(v_cfg_1227_, 2);
v_moreLeancArgs_1232_ = lean_ctor_get(v_cfg_1227_, 3);
v_moreServerOptions_1233_ = lean_ctor_get(v_cfg_1227_, 4);
v_weakLeancArgs_1234_ = lean_ctor_get(v_cfg_1227_, 5);
v_moreLinkObjs_1235_ = lean_ctor_get(v_cfg_1227_, 6);
v_moreLinkLibs_1236_ = lean_ctor_get(v_cfg_1227_, 7);
v_moreLinkArgs_1237_ = lean_ctor_get(v_cfg_1227_, 8);
v_weakLinkArgs_1238_ = lean_ctor_get(v_cfg_1227_, 9);
v_backend_1239_ = lean_ctor_get_uint8(v_cfg_1227_, sizeof(void*)*13 + 1);
v_platformIndependent_1240_ = lean_ctor_get(v_cfg_1227_, 10);
v_precompileImports_1241_ = lean_ctor_get_uint8(v_cfg_1227_, sizeof(void*)*13 + 2);
v_dynlibs_1242_ = lean_ctor_get(v_cfg_1227_, 11);
v_plugins_1243_ = lean_ctor_get(v_cfg_1227_, 12);
v_requiresModuleSystem_1244_ = lean_ctor_get_uint8(v_cfg_1227_, sizeof(void*)*13 + 3);
v_allowNonModules_1245_ = lean_ctor_get_uint8(v_cfg_1227_, sizeof(void*)*13 + 4);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_cfg_1227_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1247_ = v_cfg_1227_;
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_plugins_1243_);
lean_inc(v_dynlibs_1242_);
lean_inc(v_platformIndependent_1240_);
lean_inc(v_weakLinkArgs_1238_);
lean_inc(v_moreLinkArgs_1237_);
lean_inc(v_moreLinkLibs_1236_);
lean_inc(v_moreLinkObjs_1235_);
lean_inc(v_weakLeancArgs_1234_);
lean_inc(v_moreServerOptions_1233_);
lean_inc(v_moreLeancArgs_1232_);
lean_inc(v_weakLeanArgs_1231_);
lean_inc(v_moreLeanArgs_1230_);
lean_inc(v_leanOptions_1229_);
lean_dec(v_cfg_1227_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_apply_1(v_f_1226_, v_leanOptions_1229_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_moreLeanArgs_1230_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_weakLeanArgs_1231_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_moreLeancArgs_1232_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_moreServerOptions_1233_);
lean_ctor_set(v_reuseFailAlloc_1252_, 5, v_weakLeancArgs_1234_);
lean_ctor_set(v_reuseFailAlloc_1252_, 6, v_moreLinkObjs_1235_);
lean_ctor_set(v_reuseFailAlloc_1252_, 7, v_moreLinkLibs_1236_);
lean_ctor_set(v_reuseFailAlloc_1252_, 8, v_moreLinkArgs_1237_);
lean_ctor_set(v_reuseFailAlloc_1252_, 9, v_weakLinkArgs_1238_);
lean_ctor_set(v_reuseFailAlloc_1252_, 10, v_platformIndependent_1240_);
lean_ctor_set(v_reuseFailAlloc_1252_, 11, v_dynlibs_1242_);
lean_ctor_set(v_reuseFailAlloc_1252_, 12, v_plugins_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*13, v_buildType_1228_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*13 + 1, v_backend_1239_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*13 + 2, v_precompileImports_1241_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*13 + 4, v_allowNonModules_1245_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1256_);
lean_dec_ref(v_x_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1269_){
_start:
{
lean_object* v_moreLeanArgs_1270_; 
v_moreLeanArgs_1270_ = lean_ctor_get(v_cfg_1269_, 1);
lean_inc_ref(v_moreLeanArgs_1270_);
return v_moreLeanArgs_1270_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1271_);
lean_dec_ref(v_cfg_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1273_, lean_object* v_cfg_1274_){
_start:
{
uint8_t v_buildType_1275_; lean_object* v_leanOptions_1276_; lean_object* v_weakLeanArgs_1277_; lean_object* v_moreLeancArgs_1278_; lean_object* v_moreServerOptions_1279_; lean_object* v_weakLeancArgs_1280_; lean_object* v_moreLinkObjs_1281_; lean_object* v_moreLinkLibs_1282_; lean_object* v_moreLinkArgs_1283_; lean_object* v_weakLinkArgs_1284_; uint8_t v_backend_1285_; lean_object* v_platformIndependent_1286_; uint8_t v_precompileImports_1287_; lean_object* v_dynlibs_1288_; lean_object* v_plugins_1289_; uint8_t v_requiresModuleSystem_1290_; uint8_t v_allowNonModules_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_buildType_1275_ = lean_ctor_get_uint8(v_cfg_1274_, sizeof(void*)*13);
v_leanOptions_1276_ = lean_ctor_get(v_cfg_1274_, 0);
v_weakLeanArgs_1277_ = lean_ctor_get(v_cfg_1274_, 2);
v_moreLeancArgs_1278_ = lean_ctor_get(v_cfg_1274_, 3);
v_moreServerOptions_1279_ = lean_ctor_get(v_cfg_1274_, 4);
v_weakLeancArgs_1280_ = lean_ctor_get(v_cfg_1274_, 5);
v_moreLinkObjs_1281_ = lean_ctor_get(v_cfg_1274_, 6);
v_moreLinkLibs_1282_ = lean_ctor_get(v_cfg_1274_, 7);
v_moreLinkArgs_1283_ = lean_ctor_get(v_cfg_1274_, 8);
v_weakLinkArgs_1284_ = lean_ctor_get(v_cfg_1274_, 9);
v_backend_1285_ = lean_ctor_get_uint8(v_cfg_1274_, sizeof(void*)*13 + 1);
v_platformIndependent_1286_ = lean_ctor_get(v_cfg_1274_, 10);
v_precompileImports_1287_ = lean_ctor_get_uint8(v_cfg_1274_, sizeof(void*)*13 + 2);
v_dynlibs_1288_ = lean_ctor_get(v_cfg_1274_, 11);
v_plugins_1289_ = lean_ctor_get(v_cfg_1274_, 12);
v_requiresModuleSystem_1290_ = lean_ctor_get_uint8(v_cfg_1274_, sizeof(void*)*13 + 3);
v_allowNonModules_1291_ = lean_ctor_get_uint8(v_cfg_1274_, sizeof(void*)*13 + 4);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_cfg_1274_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_cfg_1274_, 1);
lean_dec(v_unused_1299_);
v___x_1293_ = v_cfg_1274_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_plugins_1289_);
lean_inc(v_dynlibs_1288_);
lean_inc(v_platformIndependent_1286_);
lean_inc(v_weakLinkArgs_1284_);
lean_inc(v_moreLinkArgs_1283_);
lean_inc(v_moreLinkLibs_1282_);
lean_inc(v_moreLinkObjs_1281_);
lean_inc(v_weakLeancArgs_1280_);
lean_inc(v_moreServerOptions_1279_);
lean_inc(v_moreLeancArgs_1278_);
lean_inc(v_weakLeanArgs_1277_);
lean_inc(v_leanOptions_1276_);
lean_dec(v_cfg_1274_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v_val_1273_);
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_leanOptions_1276_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_val_1273_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_weakLeanArgs_1277_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_moreLeancArgs_1278_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v_moreServerOptions_1279_);
lean_ctor_set(v_reuseFailAlloc_1297_, 5, v_weakLeancArgs_1280_);
lean_ctor_set(v_reuseFailAlloc_1297_, 6, v_moreLinkObjs_1281_);
lean_ctor_set(v_reuseFailAlloc_1297_, 7, v_moreLinkLibs_1282_);
lean_ctor_set(v_reuseFailAlloc_1297_, 8, v_moreLinkArgs_1283_);
lean_ctor_set(v_reuseFailAlloc_1297_, 9, v_weakLinkArgs_1284_);
lean_ctor_set(v_reuseFailAlloc_1297_, 10, v_platformIndependent_1286_);
lean_ctor_set(v_reuseFailAlloc_1297_, 11, v_dynlibs_1288_);
lean_ctor_set(v_reuseFailAlloc_1297_, 12, v_plugins_1289_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*13, v_buildType_1275_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*13 + 1, v_backend_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*13 + 2, v_precompileImports_1287_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1290_);
lean_ctor_set_uint8(v_reuseFailAlloc_1297_, sizeof(void*)*13 + 4, v_allowNonModules_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1300_, lean_object* v_cfg_1301_){
_start:
{
uint8_t v_buildType_1302_; lean_object* v_leanOptions_1303_; lean_object* v_moreLeanArgs_1304_; lean_object* v_weakLeanArgs_1305_; lean_object* v_moreLeancArgs_1306_; lean_object* v_moreServerOptions_1307_; lean_object* v_weakLeancArgs_1308_; lean_object* v_moreLinkObjs_1309_; lean_object* v_moreLinkLibs_1310_; lean_object* v_moreLinkArgs_1311_; lean_object* v_weakLinkArgs_1312_; uint8_t v_backend_1313_; lean_object* v_platformIndependent_1314_; uint8_t v_precompileImports_1315_; lean_object* v_dynlibs_1316_; lean_object* v_plugins_1317_; uint8_t v_requiresModuleSystem_1318_; uint8_t v_allowNonModules_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_buildType_1302_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13);
v_leanOptions_1303_ = lean_ctor_get(v_cfg_1301_, 0);
v_moreLeanArgs_1304_ = lean_ctor_get(v_cfg_1301_, 1);
v_weakLeanArgs_1305_ = lean_ctor_get(v_cfg_1301_, 2);
v_moreLeancArgs_1306_ = lean_ctor_get(v_cfg_1301_, 3);
v_moreServerOptions_1307_ = lean_ctor_get(v_cfg_1301_, 4);
v_weakLeancArgs_1308_ = lean_ctor_get(v_cfg_1301_, 5);
v_moreLinkObjs_1309_ = lean_ctor_get(v_cfg_1301_, 6);
v_moreLinkLibs_1310_ = lean_ctor_get(v_cfg_1301_, 7);
v_moreLinkArgs_1311_ = lean_ctor_get(v_cfg_1301_, 8);
v_weakLinkArgs_1312_ = lean_ctor_get(v_cfg_1301_, 9);
v_backend_1313_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13 + 1);
v_platformIndependent_1314_ = lean_ctor_get(v_cfg_1301_, 10);
v_precompileImports_1315_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13 + 2);
v_dynlibs_1316_ = lean_ctor_get(v_cfg_1301_, 11);
v_plugins_1317_ = lean_ctor_get(v_cfg_1301_, 12);
v_requiresModuleSystem_1318_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13 + 3);
v_allowNonModules_1319_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13 + 4);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_cfg_1301_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v_cfg_1301_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_plugins_1317_);
lean_inc(v_dynlibs_1316_);
lean_inc(v_platformIndependent_1314_);
lean_inc(v_weakLinkArgs_1312_);
lean_inc(v_moreLinkArgs_1311_);
lean_inc(v_moreLinkLibs_1310_);
lean_inc(v_moreLinkObjs_1309_);
lean_inc(v_weakLeancArgs_1308_);
lean_inc(v_moreServerOptions_1307_);
lean_inc(v_moreLeancArgs_1306_);
lean_inc(v_weakLeanArgs_1305_);
lean_inc(v_moreLeanArgs_1304_);
lean_inc(v_leanOptions_1303_);
lean_dec(v_cfg_1301_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_apply_1(v_f_1300_, v_moreLeanArgs_1304_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 1, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_leanOptions_1303_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_weakLeanArgs_1305_);
lean_ctor_set(v_reuseFailAlloc_1326_, 3, v_moreLeancArgs_1306_);
lean_ctor_set(v_reuseFailAlloc_1326_, 4, v_moreServerOptions_1307_);
lean_ctor_set(v_reuseFailAlloc_1326_, 5, v_weakLeancArgs_1308_);
lean_ctor_set(v_reuseFailAlloc_1326_, 6, v_moreLinkObjs_1309_);
lean_ctor_set(v_reuseFailAlloc_1326_, 7, v_moreLinkLibs_1310_);
lean_ctor_set(v_reuseFailAlloc_1326_, 8, v_moreLinkArgs_1311_);
lean_ctor_set(v_reuseFailAlloc_1326_, 9, v_weakLinkArgs_1312_);
lean_ctor_set(v_reuseFailAlloc_1326_, 10, v_platformIndependent_1314_);
lean_ctor_set(v_reuseFailAlloc_1326_, 11, v_dynlibs_1316_);
lean_ctor_set(v_reuseFailAlloc_1326_, 12, v_plugins_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*13, v_buildType_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*13 + 1, v_backend_1313_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*13 + 2, v_precompileImports_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1326_, sizeof(void*)*13 + 4, v_allowNonModules_1319_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = ((lean_object*)(l_Lake_BuildType_leanArgs___redArg___closed__0));
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1330_);
lean_dec_ref(v_x_1330_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1343_){
_start:
{
lean_object* v_weakLeanArgs_1344_; 
v_weakLeanArgs_1344_ = lean_ctor_get(v_cfg_1343_, 2);
lean_inc_ref(v_weakLeanArgs_1344_);
return v_weakLeanArgs_1344_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1345_);
lean_dec_ref(v_cfg_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1347_, lean_object* v_cfg_1348_){
_start:
{
uint8_t v_buildType_1349_; lean_object* v_leanOptions_1350_; lean_object* v_moreLeanArgs_1351_; lean_object* v_moreLeancArgs_1352_; lean_object* v_moreServerOptions_1353_; lean_object* v_weakLeancArgs_1354_; lean_object* v_moreLinkObjs_1355_; lean_object* v_moreLinkLibs_1356_; lean_object* v_moreLinkArgs_1357_; lean_object* v_weakLinkArgs_1358_; uint8_t v_backend_1359_; lean_object* v_platformIndependent_1360_; uint8_t v_precompileImports_1361_; lean_object* v_dynlibs_1362_; lean_object* v_plugins_1363_; uint8_t v_requiresModuleSystem_1364_; uint8_t v_allowNonModules_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_buildType_1349_ = lean_ctor_get_uint8(v_cfg_1348_, sizeof(void*)*13);
v_leanOptions_1350_ = lean_ctor_get(v_cfg_1348_, 0);
v_moreLeanArgs_1351_ = lean_ctor_get(v_cfg_1348_, 1);
v_moreLeancArgs_1352_ = lean_ctor_get(v_cfg_1348_, 3);
v_moreServerOptions_1353_ = lean_ctor_get(v_cfg_1348_, 4);
v_weakLeancArgs_1354_ = lean_ctor_get(v_cfg_1348_, 5);
v_moreLinkObjs_1355_ = lean_ctor_get(v_cfg_1348_, 6);
v_moreLinkLibs_1356_ = lean_ctor_get(v_cfg_1348_, 7);
v_moreLinkArgs_1357_ = lean_ctor_get(v_cfg_1348_, 8);
v_weakLinkArgs_1358_ = lean_ctor_get(v_cfg_1348_, 9);
v_backend_1359_ = lean_ctor_get_uint8(v_cfg_1348_, sizeof(void*)*13 + 1);
v_platformIndependent_1360_ = lean_ctor_get(v_cfg_1348_, 10);
v_precompileImports_1361_ = lean_ctor_get_uint8(v_cfg_1348_, sizeof(void*)*13 + 2);
v_dynlibs_1362_ = lean_ctor_get(v_cfg_1348_, 11);
v_plugins_1363_ = lean_ctor_get(v_cfg_1348_, 12);
v_requiresModuleSystem_1364_ = lean_ctor_get_uint8(v_cfg_1348_, sizeof(void*)*13 + 3);
v_allowNonModules_1365_ = lean_ctor_get_uint8(v_cfg_1348_, sizeof(void*)*13 + 4);
v_isSharedCheck_1372_ = !lean_is_exclusive(v_cfg_1348_);
if (v_isSharedCheck_1372_ == 0)
{
lean_object* v_unused_1373_; 
v_unused_1373_ = lean_ctor_get(v_cfg_1348_, 2);
lean_dec(v_unused_1373_);
v___x_1367_ = v_cfg_1348_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_plugins_1363_);
lean_inc(v_dynlibs_1362_);
lean_inc(v_platformIndependent_1360_);
lean_inc(v_weakLinkArgs_1358_);
lean_inc(v_moreLinkArgs_1357_);
lean_inc(v_moreLinkLibs_1356_);
lean_inc(v_moreLinkObjs_1355_);
lean_inc(v_weakLeancArgs_1354_);
lean_inc(v_moreServerOptions_1353_);
lean_inc(v_moreLeancArgs_1352_);
lean_inc(v_moreLeanArgs_1351_);
lean_inc(v_leanOptions_1350_);
lean_dec(v_cfg_1348_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 2, v_val_1347_);
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_leanOptions_1350_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_moreLeanArgs_1351_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_val_1347_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v_moreLeancArgs_1352_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_moreServerOptions_1353_);
lean_ctor_set(v_reuseFailAlloc_1371_, 5, v_weakLeancArgs_1354_);
lean_ctor_set(v_reuseFailAlloc_1371_, 6, v_moreLinkObjs_1355_);
lean_ctor_set(v_reuseFailAlloc_1371_, 7, v_moreLinkLibs_1356_);
lean_ctor_set(v_reuseFailAlloc_1371_, 8, v_moreLinkArgs_1357_);
lean_ctor_set(v_reuseFailAlloc_1371_, 9, v_weakLinkArgs_1358_);
lean_ctor_set(v_reuseFailAlloc_1371_, 10, v_platformIndependent_1360_);
lean_ctor_set(v_reuseFailAlloc_1371_, 11, v_dynlibs_1362_);
lean_ctor_set(v_reuseFailAlloc_1371_, 12, v_plugins_1363_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13, v_buildType_1349_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 1, v_backend_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 2, v_precompileImports_1361_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1364_);
lean_ctor_set_uint8(v_reuseFailAlloc_1371_, sizeof(void*)*13 + 4, v_allowNonModules_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1374_, lean_object* v_cfg_1375_){
_start:
{
uint8_t v_buildType_1376_; lean_object* v_leanOptions_1377_; lean_object* v_moreLeanArgs_1378_; lean_object* v_weakLeanArgs_1379_; lean_object* v_moreLeancArgs_1380_; lean_object* v_moreServerOptions_1381_; lean_object* v_weakLeancArgs_1382_; lean_object* v_moreLinkObjs_1383_; lean_object* v_moreLinkLibs_1384_; lean_object* v_moreLinkArgs_1385_; lean_object* v_weakLinkArgs_1386_; uint8_t v_backend_1387_; lean_object* v_platformIndependent_1388_; uint8_t v_precompileImports_1389_; lean_object* v_dynlibs_1390_; lean_object* v_plugins_1391_; uint8_t v_requiresModuleSystem_1392_; uint8_t v_allowNonModules_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1401_; 
v_buildType_1376_ = lean_ctor_get_uint8(v_cfg_1375_, sizeof(void*)*13);
v_leanOptions_1377_ = lean_ctor_get(v_cfg_1375_, 0);
v_moreLeanArgs_1378_ = lean_ctor_get(v_cfg_1375_, 1);
v_weakLeanArgs_1379_ = lean_ctor_get(v_cfg_1375_, 2);
v_moreLeancArgs_1380_ = lean_ctor_get(v_cfg_1375_, 3);
v_moreServerOptions_1381_ = lean_ctor_get(v_cfg_1375_, 4);
v_weakLeancArgs_1382_ = lean_ctor_get(v_cfg_1375_, 5);
v_moreLinkObjs_1383_ = lean_ctor_get(v_cfg_1375_, 6);
v_moreLinkLibs_1384_ = lean_ctor_get(v_cfg_1375_, 7);
v_moreLinkArgs_1385_ = lean_ctor_get(v_cfg_1375_, 8);
v_weakLinkArgs_1386_ = lean_ctor_get(v_cfg_1375_, 9);
v_backend_1387_ = lean_ctor_get_uint8(v_cfg_1375_, sizeof(void*)*13 + 1);
v_platformIndependent_1388_ = lean_ctor_get(v_cfg_1375_, 10);
v_precompileImports_1389_ = lean_ctor_get_uint8(v_cfg_1375_, sizeof(void*)*13 + 2);
v_dynlibs_1390_ = lean_ctor_get(v_cfg_1375_, 11);
v_plugins_1391_ = lean_ctor_get(v_cfg_1375_, 12);
v_requiresModuleSystem_1392_ = lean_ctor_get_uint8(v_cfg_1375_, sizeof(void*)*13 + 3);
v_allowNonModules_1393_ = lean_ctor_get_uint8(v_cfg_1375_, sizeof(void*)*13 + 4);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_cfg_1375_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1395_ = v_cfg_1375_;
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_plugins_1391_);
lean_inc(v_dynlibs_1390_);
lean_inc(v_platformIndependent_1388_);
lean_inc(v_weakLinkArgs_1386_);
lean_inc(v_moreLinkArgs_1385_);
lean_inc(v_moreLinkLibs_1384_);
lean_inc(v_moreLinkObjs_1383_);
lean_inc(v_weakLeancArgs_1382_);
lean_inc(v_moreServerOptions_1381_);
lean_inc(v_moreLeancArgs_1380_);
lean_inc(v_weakLeanArgs_1379_);
lean_inc(v_moreLeanArgs_1378_);
lean_inc(v_leanOptions_1377_);
lean_dec(v_cfg_1375_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1401_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1397_ = lean_apply_1(v_f_1374_, v_weakLeanArgs_1379_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 2, v___x_1397_);
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_leanOptions_1377_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_moreLeanArgs_1378_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_moreLeancArgs_1380_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_moreServerOptions_1381_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_weakLeancArgs_1382_);
lean_ctor_set(v_reuseFailAlloc_1400_, 6, v_moreLinkObjs_1383_);
lean_ctor_set(v_reuseFailAlloc_1400_, 7, v_moreLinkLibs_1384_);
lean_ctor_set(v_reuseFailAlloc_1400_, 8, v_moreLinkArgs_1385_);
lean_ctor_set(v_reuseFailAlloc_1400_, 9, v_weakLinkArgs_1386_);
lean_ctor_set(v_reuseFailAlloc_1400_, 10, v_platformIndependent_1388_);
lean_ctor_set(v_reuseFailAlloc_1400_, 11, v_dynlibs_1390_);
lean_ctor_set(v_reuseFailAlloc_1400_, 12, v_plugins_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*13, v_buildType_1376_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*13 + 1, v_backend_1387_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*13 + 2, v_precompileImports_1389_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1392_);
lean_ctor_set_uint8(v_reuseFailAlloc_1400_, sizeof(void*)*13 + 4, v_allowNonModules_1393_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1412_){
_start:
{
lean_object* v_moreLeancArgs_1413_; 
v_moreLeancArgs_1413_ = lean_ctor_get(v_cfg_1412_, 3);
lean_inc_ref(v_moreLeancArgs_1413_);
return v_moreLeancArgs_1413_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1414_);
lean_dec_ref(v_cfg_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1416_, lean_object* v_cfg_1417_){
_start:
{
uint8_t v_buildType_1418_; lean_object* v_leanOptions_1419_; lean_object* v_moreLeanArgs_1420_; lean_object* v_weakLeanArgs_1421_; lean_object* v_moreServerOptions_1422_; lean_object* v_weakLeancArgs_1423_; lean_object* v_moreLinkObjs_1424_; lean_object* v_moreLinkLibs_1425_; lean_object* v_moreLinkArgs_1426_; lean_object* v_weakLinkArgs_1427_; uint8_t v_backend_1428_; lean_object* v_platformIndependent_1429_; uint8_t v_precompileImports_1430_; lean_object* v_dynlibs_1431_; lean_object* v_plugins_1432_; uint8_t v_requiresModuleSystem_1433_; uint8_t v_allowNonModules_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
v_buildType_1418_ = lean_ctor_get_uint8(v_cfg_1417_, sizeof(void*)*13);
v_leanOptions_1419_ = lean_ctor_get(v_cfg_1417_, 0);
v_moreLeanArgs_1420_ = lean_ctor_get(v_cfg_1417_, 1);
v_weakLeanArgs_1421_ = lean_ctor_get(v_cfg_1417_, 2);
v_moreServerOptions_1422_ = lean_ctor_get(v_cfg_1417_, 4);
v_weakLeancArgs_1423_ = lean_ctor_get(v_cfg_1417_, 5);
v_moreLinkObjs_1424_ = lean_ctor_get(v_cfg_1417_, 6);
v_moreLinkLibs_1425_ = lean_ctor_get(v_cfg_1417_, 7);
v_moreLinkArgs_1426_ = lean_ctor_get(v_cfg_1417_, 8);
v_weakLinkArgs_1427_ = lean_ctor_get(v_cfg_1417_, 9);
v_backend_1428_ = lean_ctor_get_uint8(v_cfg_1417_, sizeof(void*)*13 + 1);
v_platformIndependent_1429_ = lean_ctor_get(v_cfg_1417_, 10);
v_precompileImports_1430_ = lean_ctor_get_uint8(v_cfg_1417_, sizeof(void*)*13 + 2);
v_dynlibs_1431_ = lean_ctor_get(v_cfg_1417_, 11);
v_plugins_1432_ = lean_ctor_get(v_cfg_1417_, 12);
v_requiresModuleSystem_1433_ = lean_ctor_get_uint8(v_cfg_1417_, sizeof(void*)*13 + 3);
v_allowNonModules_1434_ = lean_ctor_get_uint8(v_cfg_1417_, sizeof(void*)*13 + 4);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_cfg_1417_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_cfg_1417_, 3);
lean_dec(v_unused_1442_);
v___x_1436_ = v_cfg_1417_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_plugins_1432_);
lean_inc(v_dynlibs_1431_);
lean_inc(v_platformIndependent_1429_);
lean_inc(v_weakLinkArgs_1427_);
lean_inc(v_moreLinkArgs_1426_);
lean_inc(v_moreLinkLibs_1425_);
lean_inc(v_moreLinkObjs_1424_);
lean_inc(v_weakLeancArgs_1423_);
lean_inc(v_moreServerOptions_1422_);
lean_inc(v_weakLeanArgs_1421_);
lean_inc(v_moreLeanArgs_1420_);
lean_inc(v_leanOptions_1419_);
lean_dec(v_cfg_1417_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 3, v_val_1416_);
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_leanOptions_1419_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_moreLeanArgs_1420_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_weakLeanArgs_1421_);
lean_ctor_set(v_reuseFailAlloc_1440_, 3, v_val_1416_);
lean_ctor_set(v_reuseFailAlloc_1440_, 4, v_moreServerOptions_1422_);
lean_ctor_set(v_reuseFailAlloc_1440_, 5, v_weakLeancArgs_1423_);
lean_ctor_set(v_reuseFailAlloc_1440_, 6, v_moreLinkObjs_1424_);
lean_ctor_set(v_reuseFailAlloc_1440_, 7, v_moreLinkLibs_1425_);
lean_ctor_set(v_reuseFailAlloc_1440_, 8, v_moreLinkArgs_1426_);
lean_ctor_set(v_reuseFailAlloc_1440_, 9, v_weakLinkArgs_1427_);
lean_ctor_set(v_reuseFailAlloc_1440_, 10, v_platformIndependent_1429_);
lean_ctor_set(v_reuseFailAlloc_1440_, 11, v_dynlibs_1431_);
lean_ctor_set(v_reuseFailAlloc_1440_, 12, v_plugins_1432_);
lean_ctor_set_uint8(v_reuseFailAlloc_1440_, sizeof(void*)*13, v_buildType_1418_);
lean_ctor_set_uint8(v_reuseFailAlloc_1440_, sizeof(void*)*13 + 1, v_backend_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1440_, sizeof(void*)*13 + 2, v_precompileImports_1430_);
lean_ctor_set_uint8(v_reuseFailAlloc_1440_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1433_);
lean_ctor_set_uint8(v_reuseFailAlloc_1440_, sizeof(void*)*13 + 4, v_allowNonModules_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1443_, lean_object* v_cfg_1444_){
_start:
{
uint8_t v_buildType_1445_; lean_object* v_leanOptions_1446_; lean_object* v_moreLeanArgs_1447_; lean_object* v_weakLeanArgs_1448_; lean_object* v_moreLeancArgs_1449_; lean_object* v_moreServerOptions_1450_; lean_object* v_weakLeancArgs_1451_; lean_object* v_moreLinkObjs_1452_; lean_object* v_moreLinkLibs_1453_; lean_object* v_moreLinkArgs_1454_; lean_object* v_weakLinkArgs_1455_; uint8_t v_backend_1456_; lean_object* v_platformIndependent_1457_; uint8_t v_precompileImports_1458_; lean_object* v_dynlibs_1459_; lean_object* v_plugins_1460_; uint8_t v_requiresModuleSystem_1461_; uint8_t v_allowNonModules_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1470_; 
v_buildType_1445_ = lean_ctor_get_uint8(v_cfg_1444_, sizeof(void*)*13);
v_leanOptions_1446_ = lean_ctor_get(v_cfg_1444_, 0);
v_moreLeanArgs_1447_ = lean_ctor_get(v_cfg_1444_, 1);
v_weakLeanArgs_1448_ = lean_ctor_get(v_cfg_1444_, 2);
v_moreLeancArgs_1449_ = lean_ctor_get(v_cfg_1444_, 3);
v_moreServerOptions_1450_ = lean_ctor_get(v_cfg_1444_, 4);
v_weakLeancArgs_1451_ = lean_ctor_get(v_cfg_1444_, 5);
v_moreLinkObjs_1452_ = lean_ctor_get(v_cfg_1444_, 6);
v_moreLinkLibs_1453_ = lean_ctor_get(v_cfg_1444_, 7);
v_moreLinkArgs_1454_ = lean_ctor_get(v_cfg_1444_, 8);
v_weakLinkArgs_1455_ = lean_ctor_get(v_cfg_1444_, 9);
v_backend_1456_ = lean_ctor_get_uint8(v_cfg_1444_, sizeof(void*)*13 + 1);
v_platformIndependent_1457_ = lean_ctor_get(v_cfg_1444_, 10);
v_precompileImports_1458_ = lean_ctor_get_uint8(v_cfg_1444_, sizeof(void*)*13 + 2);
v_dynlibs_1459_ = lean_ctor_get(v_cfg_1444_, 11);
v_plugins_1460_ = lean_ctor_get(v_cfg_1444_, 12);
v_requiresModuleSystem_1461_ = lean_ctor_get_uint8(v_cfg_1444_, sizeof(void*)*13 + 3);
v_allowNonModules_1462_ = lean_ctor_get_uint8(v_cfg_1444_, sizeof(void*)*13 + 4);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_cfg_1444_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1464_ = v_cfg_1444_;
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_plugins_1460_);
lean_inc(v_dynlibs_1459_);
lean_inc(v_platformIndependent_1457_);
lean_inc(v_weakLinkArgs_1455_);
lean_inc(v_moreLinkArgs_1454_);
lean_inc(v_moreLinkLibs_1453_);
lean_inc(v_moreLinkObjs_1452_);
lean_inc(v_weakLeancArgs_1451_);
lean_inc(v_moreServerOptions_1450_);
lean_inc(v_moreLeancArgs_1449_);
lean_inc(v_weakLeanArgs_1448_);
lean_inc(v_moreLeanArgs_1447_);
lean_inc(v_leanOptions_1446_);
lean_dec(v_cfg_1444_);
v___x_1464_ = lean_box(0);
v_isShared_1465_ = v_isSharedCheck_1470_;
goto v_resetjp_1463_;
}
v_resetjp_1463_:
{
lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1466_ = lean_apply_1(v_f_1443_, v_moreLeancArgs_1449_);
if (v_isShared_1465_ == 0)
{
lean_ctor_set(v___x_1464_, 3, v___x_1466_);
v___x_1468_ = v___x_1464_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_leanOptions_1446_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_moreLeanArgs_1447_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_weakLeanArgs_1448_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_moreServerOptions_1450_);
lean_ctor_set(v_reuseFailAlloc_1469_, 5, v_weakLeancArgs_1451_);
lean_ctor_set(v_reuseFailAlloc_1469_, 6, v_moreLinkObjs_1452_);
lean_ctor_set(v_reuseFailAlloc_1469_, 7, v_moreLinkLibs_1453_);
lean_ctor_set(v_reuseFailAlloc_1469_, 8, v_moreLinkArgs_1454_);
lean_ctor_set(v_reuseFailAlloc_1469_, 9, v_weakLinkArgs_1455_);
lean_ctor_set(v_reuseFailAlloc_1469_, 10, v_platformIndependent_1457_);
lean_ctor_set(v_reuseFailAlloc_1469_, 11, v_dynlibs_1459_);
lean_ctor_set(v_reuseFailAlloc_1469_, 12, v_plugins_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*13, v_buildType_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*13 + 1, v_backend_1456_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*13 + 2, v_precompileImports_1458_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1461_);
lean_ctor_set_uint8(v_reuseFailAlloc_1469_, sizeof(void*)*13 + 4, v_allowNonModules_1462_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1481_){
_start:
{
lean_object* v_moreServerOptions_1482_; 
v_moreServerOptions_1482_ = lean_ctor_get(v_cfg_1481_, 4);
lean_inc_ref(v_moreServerOptions_1482_);
return v_moreServerOptions_1482_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1483_);
lean_dec_ref(v_cfg_1483_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1485_, lean_object* v_cfg_1486_){
_start:
{
uint8_t v_buildType_1487_; lean_object* v_leanOptions_1488_; lean_object* v_moreLeanArgs_1489_; lean_object* v_weakLeanArgs_1490_; lean_object* v_moreLeancArgs_1491_; lean_object* v_weakLeancArgs_1492_; lean_object* v_moreLinkObjs_1493_; lean_object* v_moreLinkLibs_1494_; lean_object* v_moreLinkArgs_1495_; lean_object* v_weakLinkArgs_1496_; uint8_t v_backend_1497_; lean_object* v_platformIndependent_1498_; uint8_t v_precompileImports_1499_; lean_object* v_dynlibs_1500_; lean_object* v_plugins_1501_; uint8_t v_requiresModuleSystem_1502_; uint8_t v_allowNonModules_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
v_buildType_1487_ = lean_ctor_get_uint8(v_cfg_1486_, sizeof(void*)*13);
v_leanOptions_1488_ = lean_ctor_get(v_cfg_1486_, 0);
v_moreLeanArgs_1489_ = lean_ctor_get(v_cfg_1486_, 1);
v_weakLeanArgs_1490_ = lean_ctor_get(v_cfg_1486_, 2);
v_moreLeancArgs_1491_ = lean_ctor_get(v_cfg_1486_, 3);
v_weakLeancArgs_1492_ = lean_ctor_get(v_cfg_1486_, 5);
v_moreLinkObjs_1493_ = lean_ctor_get(v_cfg_1486_, 6);
v_moreLinkLibs_1494_ = lean_ctor_get(v_cfg_1486_, 7);
v_moreLinkArgs_1495_ = lean_ctor_get(v_cfg_1486_, 8);
v_weakLinkArgs_1496_ = lean_ctor_get(v_cfg_1486_, 9);
v_backend_1497_ = lean_ctor_get_uint8(v_cfg_1486_, sizeof(void*)*13 + 1);
v_platformIndependent_1498_ = lean_ctor_get(v_cfg_1486_, 10);
v_precompileImports_1499_ = lean_ctor_get_uint8(v_cfg_1486_, sizeof(void*)*13 + 2);
v_dynlibs_1500_ = lean_ctor_get(v_cfg_1486_, 11);
v_plugins_1501_ = lean_ctor_get(v_cfg_1486_, 12);
v_requiresModuleSystem_1502_ = lean_ctor_get_uint8(v_cfg_1486_, sizeof(void*)*13 + 3);
v_allowNonModules_1503_ = lean_ctor_get_uint8(v_cfg_1486_, sizeof(void*)*13 + 4);
v_isSharedCheck_1510_ = !lean_is_exclusive(v_cfg_1486_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v_cfg_1486_, 4);
lean_dec(v_unused_1511_);
v___x_1505_ = v_cfg_1486_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_plugins_1501_);
lean_inc(v_dynlibs_1500_);
lean_inc(v_platformIndependent_1498_);
lean_inc(v_weakLinkArgs_1496_);
lean_inc(v_moreLinkArgs_1495_);
lean_inc(v_moreLinkLibs_1494_);
lean_inc(v_moreLinkObjs_1493_);
lean_inc(v_weakLeancArgs_1492_);
lean_inc(v_moreLeancArgs_1491_);
lean_inc(v_weakLeanArgs_1490_);
lean_inc(v_moreLeanArgs_1489_);
lean_inc(v_leanOptions_1488_);
lean_dec(v_cfg_1486_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 4, v_val_1485_);
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_leanOptions_1488_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_moreLeanArgs_1489_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_weakLeanArgs_1490_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_moreLeancArgs_1491_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_val_1485_);
lean_ctor_set(v_reuseFailAlloc_1509_, 5, v_weakLeancArgs_1492_);
lean_ctor_set(v_reuseFailAlloc_1509_, 6, v_moreLinkObjs_1493_);
lean_ctor_set(v_reuseFailAlloc_1509_, 7, v_moreLinkLibs_1494_);
lean_ctor_set(v_reuseFailAlloc_1509_, 8, v_moreLinkArgs_1495_);
lean_ctor_set(v_reuseFailAlloc_1509_, 9, v_weakLinkArgs_1496_);
lean_ctor_set(v_reuseFailAlloc_1509_, 10, v_platformIndependent_1498_);
lean_ctor_set(v_reuseFailAlloc_1509_, 11, v_dynlibs_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 12, v_plugins_1501_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*13, v_buildType_1487_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*13 + 1, v_backend_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*13 + 2, v_precompileImports_1499_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1502_);
lean_ctor_set_uint8(v_reuseFailAlloc_1509_, sizeof(void*)*13 + 4, v_allowNonModules_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1512_, lean_object* v_cfg_1513_){
_start:
{
uint8_t v_buildType_1514_; lean_object* v_leanOptions_1515_; lean_object* v_moreLeanArgs_1516_; lean_object* v_weakLeanArgs_1517_; lean_object* v_moreLeancArgs_1518_; lean_object* v_moreServerOptions_1519_; lean_object* v_weakLeancArgs_1520_; lean_object* v_moreLinkObjs_1521_; lean_object* v_moreLinkLibs_1522_; lean_object* v_moreLinkArgs_1523_; lean_object* v_weakLinkArgs_1524_; uint8_t v_backend_1525_; lean_object* v_platformIndependent_1526_; uint8_t v_precompileImports_1527_; lean_object* v_dynlibs_1528_; lean_object* v_plugins_1529_; uint8_t v_requiresModuleSystem_1530_; uint8_t v_allowNonModules_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1539_; 
v_buildType_1514_ = lean_ctor_get_uint8(v_cfg_1513_, sizeof(void*)*13);
v_leanOptions_1515_ = lean_ctor_get(v_cfg_1513_, 0);
v_moreLeanArgs_1516_ = lean_ctor_get(v_cfg_1513_, 1);
v_weakLeanArgs_1517_ = lean_ctor_get(v_cfg_1513_, 2);
v_moreLeancArgs_1518_ = lean_ctor_get(v_cfg_1513_, 3);
v_moreServerOptions_1519_ = lean_ctor_get(v_cfg_1513_, 4);
v_weakLeancArgs_1520_ = lean_ctor_get(v_cfg_1513_, 5);
v_moreLinkObjs_1521_ = lean_ctor_get(v_cfg_1513_, 6);
v_moreLinkLibs_1522_ = lean_ctor_get(v_cfg_1513_, 7);
v_moreLinkArgs_1523_ = lean_ctor_get(v_cfg_1513_, 8);
v_weakLinkArgs_1524_ = lean_ctor_get(v_cfg_1513_, 9);
v_backend_1525_ = lean_ctor_get_uint8(v_cfg_1513_, sizeof(void*)*13 + 1);
v_platformIndependent_1526_ = lean_ctor_get(v_cfg_1513_, 10);
v_precompileImports_1527_ = lean_ctor_get_uint8(v_cfg_1513_, sizeof(void*)*13 + 2);
v_dynlibs_1528_ = lean_ctor_get(v_cfg_1513_, 11);
v_plugins_1529_ = lean_ctor_get(v_cfg_1513_, 12);
v_requiresModuleSystem_1530_ = lean_ctor_get_uint8(v_cfg_1513_, sizeof(void*)*13 + 3);
v_allowNonModules_1531_ = lean_ctor_get_uint8(v_cfg_1513_, sizeof(void*)*13 + 4);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_cfg_1513_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1533_ = v_cfg_1513_;
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_plugins_1529_);
lean_inc(v_dynlibs_1528_);
lean_inc(v_platformIndependent_1526_);
lean_inc(v_weakLinkArgs_1524_);
lean_inc(v_moreLinkArgs_1523_);
lean_inc(v_moreLinkLibs_1522_);
lean_inc(v_moreLinkObjs_1521_);
lean_inc(v_weakLeancArgs_1520_);
lean_inc(v_moreServerOptions_1519_);
lean_inc(v_moreLeancArgs_1518_);
lean_inc(v_weakLeanArgs_1517_);
lean_inc(v_moreLeanArgs_1516_);
lean_inc(v_leanOptions_1515_);
lean_dec(v_cfg_1513_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = lean_apply_1(v_f_1512_, v_moreServerOptions_1519_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v___x_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_leanOptions_1515_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_moreLeanArgs_1516_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_weakLeanArgs_1517_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_moreLeancArgs_1518_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1538_, 5, v_weakLeancArgs_1520_);
lean_ctor_set(v_reuseFailAlloc_1538_, 6, v_moreLinkObjs_1521_);
lean_ctor_set(v_reuseFailAlloc_1538_, 7, v_moreLinkLibs_1522_);
lean_ctor_set(v_reuseFailAlloc_1538_, 8, v_moreLinkArgs_1523_);
lean_ctor_set(v_reuseFailAlloc_1538_, 9, v_weakLinkArgs_1524_);
lean_ctor_set(v_reuseFailAlloc_1538_, 10, v_platformIndependent_1526_);
lean_ctor_set(v_reuseFailAlloc_1538_, 11, v_dynlibs_1528_);
lean_ctor_set(v_reuseFailAlloc_1538_, 12, v_plugins_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*13, v_buildType_1514_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*13 + 1, v_backend_1525_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*13 + 2, v_precompileImports_1527_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1538_, sizeof(void*)*13 + 4, v_allowNonModules_1531_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1550_){
_start:
{
lean_object* v_weakLeancArgs_1551_; 
v_weakLeancArgs_1551_ = lean_ctor_get(v_cfg_1550_, 5);
lean_inc_ref(v_weakLeancArgs_1551_);
return v_weakLeancArgs_1551_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1552_);
lean_dec_ref(v_cfg_1552_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1554_, lean_object* v_cfg_1555_){
_start:
{
uint8_t v_buildType_1556_; lean_object* v_leanOptions_1557_; lean_object* v_moreLeanArgs_1558_; lean_object* v_weakLeanArgs_1559_; lean_object* v_moreLeancArgs_1560_; lean_object* v_moreServerOptions_1561_; lean_object* v_moreLinkObjs_1562_; lean_object* v_moreLinkLibs_1563_; lean_object* v_moreLinkArgs_1564_; lean_object* v_weakLinkArgs_1565_; uint8_t v_backend_1566_; lean_object* v_platformIndependent_1567_; uint8_t v_precompileImports_1568_; lean_object* v_dynlibs_1569_; lean_object* v_plugins_1570_; uint8_t v_requiresModuleSystem_1571_; uint8_t v_allowNonModules_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
v_buildType_1556_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*13);
v_leanOptions_1557_ = lean_ctor_get(v_cfg_1555_, 0);
v_moreLeanArgs_1558_ = lean_ctor_get(v_cfg_1555_, 1);
v_weakLeanArgs_1559_ = lean_ctor_get(v_cfg_1555_, 2);
v_moreLeancArgs_1560_ = lean_ctor_get(v_cfg_1555_, 3);
v_moreServerOptions_1561_ = lean_ctor_get(v_cfg_1555_, 4);
v_moreLinkObjs_1562_ = lean_ctor_get(v_cfg_1555_, 6);
v_moreLinkLibs_1563_ = lean_ctor_get(v_cfg_1555_, 7);
v_moreLinkArgs_1564_ = lean_ctor_get(v_cfg_1555_, 8);
v_weakLinkArgs_1565_ = lean_ctor_get(v_cfg_1555_, 9);
v_backend_1566_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*13 + 1);
v_platformIndependent_1567_ = lean_ctor_get(v_cfg_1555_, 10);
v_precompileImports_1568_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*13 + 2);
v_dynlibs_1569_ = lean_ctor_get(v_cfg_1555_, 11);
v_plugins_1570_ = lean_ctor_get(v_cfg_1555_, 12);
v_requiresModuleSystem_1571_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*13 + 3);
v_allowNonModules_1572_ = lean_ctor_get_uint8(v_cfg_1555_, sizeof(void*)*13 + 4);
v_isSharedCheck_1579_ = !lean_is_exclusive(v_cfg_1555_);
if (v_isSharedCheck_1579_ == 0)
{
lean_object* v_unused_1580_; 
v_unused_1580_ = lean_ctor_get(v_cfg_1555_, 5);
lean_dec(v_unused_1580_);
v___x_1574_ = v_cfg_1555_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_plugins_1570_);
lean_inc(v_dynlibs_1569_);
lean_inc(v_platformIndependent_1567_);
lean_inc(v_weakLinkArgs_1565_);
lean_inc(v_moreLinkArgs_1564_);
lean_inc(v_moreLinkLibs_1563_);
lean_inc(v_moreLinkObjs_1562_);
lean_inc(v_moreServerOptions_1561_);
lean_inc(v_moreLeancArgs_1560_);
lean_inc(v_weakLeanArgs_1559_);
lean_inc(v_moreLeanArgs_1558_);
lean_inc(v_leanOptions_1557_);
lean_dec(v_cfg_1555_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 5, v_val_1554_);
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_leanOptions_1557_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_moreLeanArgs_1558_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_weakLeanArgs_1559_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_moreLeancArgs_1560_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_moreServerOptions_1561_);
lean_ctor_set(v_reuseFailAlloc_1578_, 5, v_val_1554_);
lean_ctor_set(v_reuseFailAlloc_1578_, 6, v_moreLinkObjs_1562_);
lean_ctor_set(v_reuseFailAlloc_1578_, 7, v_moreLinkLibs_1563_);
lean_ctor_set(v_reuseFailAlloc_1578_, 8, v_moreLinkArgs_1564_);
lean_ctor_set(v_reuseFailAlloc_1578_, 9, v_weakLinkArgs_1565_);
lean_ctor_set(v_reuseFailAlloc_1578_, 10, v_platformIndependent_1567_);
lean_ctor_set(v_reuseFailAlloc_1578_, 11, v_dynlibs_1569_);
lean_ctor_set(v_reuseFailAlloc_1578_, 12, v_plugins_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1578_, sizeof(void*)*13, v_buildType_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1578_, sizeof(void*)*13 + 1, v_backend_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1578_, sizeof(void*)*13 + 2, v_precompileImports_1568_);
lean_ctor_set_uint8(v_reuseFailAlloc_1578_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1578_, sizeof(void*)*13 + 4, v_allowNonModules_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1581_, lean_object* v_cfg_1582_){
_start:
{
uint8_t v_buildType_1583_; lean_object* v_leanOptions_1584_; lean_object* v_moreLeanArgs_1585_; lean_object* v_weakLeanArgs_1586_; lean_object* v_moreLeancArgs_1587_; lean_object* v_moreServerOptions_1588_; lean_object* v_weakLeancArgs_1589_; lean_object* v_moreLinkObjs_1590_; lean_object* v_moreLinkLibs_1591_; lean_object* v_moreLinkArgs_1592_; lean_object* v_weakLinkArgs_1593_; uint8_t v_backend_1594_; lean_object* v_platformIndependent_1595_; uint8_t v_precompileImports_1596_; lean_object* v_dynlibs_1597_; lean_object* v_plugins_1598_; uint8_t v_requiresModuleSystem_1599_; uint8_t v_allowNonModules_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
v_buildType_1583_ = lean_ctor_get_uint8(v_cfg_1582_, sizeof(void*)*13);
v_leanOptions_1584_ = lean_ctor_get(v_cfg_1582_, 0);
v_moreLeanArgs_1585_ = lean_ctor_get(v_cfg_1582_, 1);
v_weakLeanArgs_1586_ = lean_ctor_get(v_cfg_1582_, 2);
v_moreLeancArgs_1587_ = lean_ctor_get(v_cfg_1582_, 3);
v_moreServerOptions_1588_ = lean_ctor_get(v_cfg_1582_, 4);
v_weakLeancArgs_1589_ = lean_ctor_get(v_cfg_1582_, 5);
v_moreLinkObjs_1590_ = lean_ctor_get(v_cfg_1582_, 6);
v_moreLinkLibs_1591_ = lean_ctor_get(v_cfg_1582_, 7);
v_moreLinkArgs_1592_ = lean_ctor_get(v_cfg_1582_, 8);
v_weakLinkArgs_1593_ = lean_ctor_get(v_cfg_1582_, 9);
v_backend_1594_ = lean_ctor_get_uint8(v_cfg_1582_, sizeof(void*)*13 + 1);
v_platformIndependent_1595_ = lean_ctor_get(v_cfg_1582_, 10);
v_precompileImports_1596_ = lean_ctor_get_uint8(v_cfg_1582_, sizeof(void*)*13 + 2);
v_dynlibs_1597_ = lean_ctor_get(v_cfg_1582_, 11);
v_plugins_1598_ = lean_ctor_get(v_cfg_1582_, 12);
v_requiresModuleSystem_1599_ = lean_ctor_get_uint8(v_cfg_1582_, sizeof(void*)*13 + 3);
v_allowNonModules_1600_ = lean_ctor_get_uint8(v_cfg_1582_, sizeof(void*)*13 + 4);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_cfg_1582_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1602_ = v_cfg_1582_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_plugins_1598_);
lean_inc(v_dynlibs_1597_);
lean_inc(v_platformIndependent_1595_);
lean_inc(v_weakLinkArgs_1593_);
lean_inc(v_moreLinkArgs_1592_);
lean_inc(v_moreLinkLibs_1591_);
lean_inc(v_moreLinkObjs_1590_);
lean_inc(v_weakLeancArgs_1589_);
lean_inc(v_moreServerOptions_1588_);
lean_inc(v_moreLeancArgs_1587_);
lean_inc(v_weakLeanArgs_1586_);
lean_inc(v_moreLeanArgs_1585_);
lean_inc(v_leanOptions_1584_);
lean_dec(v_cfg_1582_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_apply_1(v_f_1581_, v_weakLeancArgs_1589_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 5, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_leanOptions_1584_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_moreLeanArgs_1585_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_weakLeanArgs_1586_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_moreLeancArgs_1587_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_moreServerOptions_1588_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1607_, 6, v_moreLinkObjs_1590_);
lean_ctor_set(v_reuseFailAlloc_1607_, 7, v_moreLinkLibs_1591_);
lean_ctor_set(v_reuseFailAlloc_1607_, 8, v_moreLinkArgs_1592_);
lean_ctor_set(v_reuseFailAlloc_1607_, 9, v_weakLinkArgs_1593_);
lean_ctor_set(v_reuseFailAlloc_1607_, 10, v_platformIndependent_1595_);
lean_ctor_set(v_reuseFailAlloc_1607_, 11, v_dynlibs_1597_);
lean_ctor_set(v_reuseFailAlloc_1607_, 12, v_plugins_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*13, v_buildType_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*13 + 1, v_backend_1594_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*13 + 2, v_precompileImports_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1599_);
lean_ctor_set_uint8(v_reuseFailAlloc_1607_, sizeof(void*)*13 + 4, v_allowNonModules_1600_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1619_){
_start:
{
lean_object* v_moreLinkObjs_1620_; 
v_moreLinkObjs_1620_ = lean_ctor_get(v_cfg_1619_, 6);
lean_inc_ref(v_moreLinkObjs_1620_);
return v_moreLinkObjs_1620_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1621_);
lean_dec_ref(v_cfg_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1623_, lean_object* v_cfg_1624_){
_start:
{
uint8_t v_buildType_1625_; lean_object* v_leanOptions_1626_; lean_object* v_moreLeanArgs_1627_; lean_object* v_weakLeanArgs_1628_; lean_object* v_moreLeancArgs_1629_; lean_object* v_moreServerOptions_1630_; lean_object* v_weakLeancArgs_1631_; lean_object* v_moreLinkLibs_1632_; lean_object* v_moreLinkArgs_1633_; lean_object* v_weakLinkArgs_1634_; uint8_t v_backend_1635_; lean_object* v_platformIndependent_1636_; uint8_t v_precompileImports_1637_; lean_object* v_dynlibs_1638_; lean_object* v_plugins_1639_; uint8_t v_requiresModuleSystem_1640_; uint8_t v_allowNonModules_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v_buildType_1625_ = lean_ctor_get_uint8(v_cfg_1624_, sizeof(void*)*13);
v_leanOptions_1626_ = lean_ctor_get(v_cfg_1624_, 0);
v_moreLeanArgs_1627_ = lean_ctor_get(v_cfg_1624_, 1);
v_weakLeanArgs_1628_ = lean_ctor_get(v_cfg_1624_, 2);
v_moreLeancArgs_1629_ = lean_ctor_get(v_cfg_1624_, 3);
v_moreServerOptions_1630_ = lean_ctor_get(v_cfg_1624_, 4);
v_weakLeancArgs_1631_ = lean_ctor_get(v_cfg_1624_, 5);
v_moreLinkLibs_1632_ = lean_ctor_get(v_cfg_1624_, 7);
v_moreLinkArgs_1633_ = lean_ctor_get(v_cfg_1624_, 8);
v_weakLinkArgs_1634_ = lean_ctor_get(v_cfg_1624_, 9);
v_backend_1635_ = lean_ctor_get_uint8(v_cfg_1624_, sizeof(void*)*13 + 1);
v_platformIndependent_1636_ = lean_ctor_get(v_cfg_1624_, 10);
v_precompileImports_1637_ = lean_ctor_get_uint8(v_cfg_1624_, sizeof(void*)*13 + 2);
v_dynlibs_1638_ = lean_ctor_get(v_cfg_1624_, 11);
v_plugins_1639_ = lean_ctor_get(v_cfg_1624_, 12);
v_requiresModuleSystem_1640_ = lean_ctor_get_uint8(v_cfg_1624_, sizeof(void*)*13 + 3);
v_allowNonModules_1641_ = lean_ctor_get_uint8(v_cfg_1624_, sizeof(void*)*13 + 4);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_cfg_1624_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; 
v_unused_1649_ = lean_ctor_get(v_cfg_1624_, 6);
lean_dec(v_unused_1649_);
v___x_1643_ = v_cfg_1624_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_plugins_1639_);
lean_inc(v_dynlibs_1638_);
lean_inc(v_platformIndependent_1636_);
lean_inc(v_weakLinkArgs_1634_);
lean_inc(v_moreLinkArgs_1633_);
lean_inc(v_moreLinkLibs_1632_);
lean_inc(v_weakLeancArgs_1631_);
lean_inc(v_moreServerOptions_1630_);
lean_inc(v_moreLeancArgs_1629_);
lean_inc(v_weakLeanArgs_1628_);
lean_inc(v_moreLeanArgs_1627_);
lean_inc(v_leanOptions_1626_);
lean_dec(v_cfg_1624_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 6, v_val_1623_);
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_leanOptions_1626_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_moreLeanArgs_1627_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_weakLeanArgs_1628_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_moreLeancArgs_1629_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_moreServerOptions_1630_);
lean_ctor_set(v_reuseFailAlloc_1647_, 5, v_weakLeancArgs_1631_);
lean_ctor_set(v_reuseFailAlloc_1647_, 6, v_val_1623_);
lean_ctor_set(v_reuseFailAlloc_1647_, 7, v_moreLinkLibs_1632_);
lean_ctor_set(v_reuseFailAlloc_1647_, 8, v_moreLinkArgs_1633_);
lean_ctor_set(v_reuseFailAlloc_1647_, 9, v_weakLinkArgs_1634_);
lean_ctor_set(v_reuseFailAlloc_1647_, 10, v_platformIndependent_1636_);
lean_ctor_set(v_reuseFailAlloc_1647_, 11, v_dynlibs_1638_);
lean_ctor_set(v_reuseFailAlloc_1647_, 12, v_plugins_1639_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*13, v_buildType_1625_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*13 + 1, v_backend_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*13 + 2, v_precompileImports_1637_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1640_);
lean_ctor_set_uint8(v_reuseFailAlloc_1647_, sizeof(void*)*13 + 4, v_allowNonModules_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1650_, lean_object* v_cfg_1651_){
_start:
{
uint8_t v_buildType_1652_; lean_object* v_leanOptions_1653_; lean_object* v_moreLeanArgs_1654_; lean_object* v_weakLeanArgs_1655_; lean_object* v_moreLeancArgs_1656_; lean_object* v_moreServerOptions_1657_; lean_object* v_weakLeancArgs_1658_; lean_object* v_moreLinkObjs_1659_; lean_object* v_moreLinkLibs_1660_; lean_object* v_moreLinkArgs_1661_; lean_object* v_weakLinkArgs_1662_; uint8_t v_backend_1663_; lean_object* v_platformIndependent_1664_; uint8_t v_precompileImports_1665_; lean_object* v_dynlibs_1666_; lean_object* v_plugins_1667_; uint8_t v_requiresModuleSystem_1668_; uint8_t v_allowNonModules_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1677_; 
v_buildType_1652_ = lean_ctor_get_uint8(v_cfg_1651_, sizeof(void*)*13);
v_leanOptions_1653_ = lean_ctor_get(v_cfg_1651_, 0);
v_moreLeanArgs_1654_ = lean_ctor_get(v_cfg_1651_, 1);
v_weakLeanArgs_1655_ = lean_ctor_get(v_cfg_1651_, 2);
v_moreLeancArgs_1656_ = lean_ctor_get(v_cfg_1651_, 3);
v_moreServerOptions_1657_ = lean_ctor_get(v_cfg_1651_, 4);
v_weakLeancArgs_1658_ = lean_ctor_get(v_cfg_1651_, 5);
v_moreLinkObjs_1659_ = lean_ctor_get(v_cfg_1651_, 6);
v_moreLinkLibs_1660_ = lean_ctor_get(v_cfg_1651_, 7);
v_moreLinkArgs_1661_ = lean_ctor_get(v_cfg_1651_, 8);
v_weakLinkArgs_1662_ = lean_ctor_get(v_cfg_1651_, 9);
v_backend_1663_ = lean_ctor_get_uint8(v_cfg_1651_, sizeof(void*)*13 + 1);
v_platformIndependent_1664_ = lean_ctor_get(v_cfg_1651_, 10);
v_precompileImports_1665_ = lean_ctor_get_uint8(v_cfg_1651_, sizeof(void*)*13 + 2);
v_dynlibs_1666_ = lean_ctor_get(v_cfg_1651_, 11);
v_plugins_1667_ = lean_ctor_get(v_cfg_1651_, 12);
v_requiresModuleSystem_1668_ = lean_ctor_get_uint8(v_cfg_1651_, sizeof(void*)*13 + 3);
v_allowNonModules_1669_ = lean_ctor_get_uint8(v_cfg_1651_, sizeof(void*)*13 + 4);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_cfg_1651_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1671_ = v_cfg_1651_;
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_plugins_1667_);
lean_inc(v_dynlibs_1666_);
lean_inc(v_platformIndependent_1664_);
lean_inc(v_weakLinkArgs_1662_);
lean_inc(v_moreLinkArgs_1661_);
lean_inc(v_moreLinkLibs_1660_);
lean_inc(v_moreLinkObjs_1659_);
lean_inc(v_weakLeancArgs_1658_);
lean_inc(v_moreServerOptions_1657_);
lean_inc(v_moreLeancArgs_1656_);
lean_inc(v_weakLeanArgs_1655_);
lean_inc(v_moreLeanArgs_1654_);
lean_inc(v_leanOptions_1653_);
lean_dec(v_cfg_1651_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1677_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
v___x_1673_ = lean_apply_1(v_f_1650_, v_moreLinkObjs_1659_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 6, v___x_1673_);
v___x_1675_ = v___x_1671_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_leanOptions_1653_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_moreLeanArgs_1654_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_weakLeanArgs_1655_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_moreLeancArgs_1656_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v_moreServerOptions_1657_);
lean_ctor_set(v_reuseFailAlloc_1676_, 5, v_weakLeancArgs_1658_);
lean_ctor_set(v_reuseFailAlloc_1676_, 6, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1676_, 7, v_moreLinkLibs_1660_);
lean_ctor_set(v_reuseFailAlloc_1676_, 8, v_moreLinkArgs_1661_);
lean_ctor_set(v_reuseFailAlloc_1676_, 9, v_weakLinkArgs_1662_);
lean_ctor_set(v_reuseFailAlloc_1676_, 10, v_platformIndependent_1664_);
lean_ctor_set(v_reuseFailAlloc_1676_, 11, v_dynlibs_1666_);
lean_ctor_set(v_reuseFailAlloc_1676_, 12, v_plugins_1667_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13, v_buildType_1652_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 1, v_backend_1663_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 2, v_precompileImports_1665_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1668_);
lean_ctor_set_uint8(v_reuseFailAlloc_1676_, sizeof(void*)*13 + 4, v_allowNonModules_1669_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1682_);
lean_dec_ref(v_x_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1695_){
_start:
{
lean_object* v_moreLinkLibs_1696_; 
v_moreLinkLibs_1696_ = lean_ctor_get(v_cfg_1695_, 7);
lean_inc_ref(v_moreLinkLibs_1696_);
return v_moreLinkLibs_1696_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1697_);
lean_dec_ref(v_cfg_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1699_, lean_object* v_cfg_1700_){
_start:
{
uint8_t v_buildType_1701_; lean_object* v_leanOptions_1702_; lean_object* v_moreLeanArgs_1703_; lean_object* v_weakLeanArgs_1704_; lean_object* v_moreLeancArgs_1705_; lean_object* v_moreServerOptions_1706_; lean_object* v_weakLeancArgs_1707_; lean_object* v_moreLinkObjs_1708_; lean_object* v_moreLinkArgs_1709_; lean_object* v_weakLinkArgs_1710_; uint8_t v_backend_1711_; lean_object* v_platformIndependent_1712_; uint8_t v_precompileImports_1713_; lean_object* v_dynlibs_1714_; lean_object* v_plugins_1715_; uint8_t v_requiresModuleSystem_1716_; uint8_t v_allowNonModules_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_buildType_1701_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13);
v_leanOptions_1702_ = lean_ctor_get(v_cfg_1700_, 0);
v_moreLeanArgs_1703_ = lean_ctor_get(v_cfg_1700_, 1);
v_weakLeanArgs_1704_ = lean_ctor_get(v_cfg_1700_, 2);
v_moreLeancArgs_1705_ = lean_ctor_get(v_cfg_1700_, 3);
v_moreServerOptions_1706_ = lean_ctor_get(v_cfg_1700_, 4);
v_weakLeancArgs_1707_ = lean_ctor_get(v_cfg_1700_, 5);
v_moreLinkObjs_1708_ = lean_ctor_get(v_cfg_1700_, 6);
v_moreLinkArgs_1709_ = lean_ctor_get(v_cfg_1700_, 8);
v_weakLinkArgs_1710_ = lean_ctor_get(v_cfg_1700_, 9);
v_backend_1711_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13 + 1);
v_platformIndependent_1712_ = lean_ctor_get(v_cfg_1700_, 10);
v_precompileImports_1713_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13 + 2);
v_dynlibs_1714_ = lean_ctor_get(v_cfg_1700_, 11);
v_plugins_1715_ = lean_ctor_get(v_cfg_1700_, 12);
v_requiresModuleSystem_1716_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13 + 3);
v_allowNonModules_1717_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13 + 4);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_cfg_1700_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v_cfg_1700_, 7);
lean_dec(v_unused_1725_);
v___x_1719_ = v_cfg_1700_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_plugins_1715_);
lean_inc(v_dynlibs_1714_);
lean_inc(v_platformIndependent_1712_);
lean_inc(v_weakLinkArgs_1710_);
lean_inc(v_moreLinkArgs_1709_);
lean_inc(v_moreLinkObjs_1708_);
lean_inc(v_weakLeancArgs_1707_);
lean_inc(v_moreServerOptions_1706_);
lean_inc(v_moreLeancArgs_1705_);
lean_inc(v_weakLeanArgs_1704_);
lean_inc(v_moreLeanArgs_1703_);
lean_inc(v_leanOptions_1702_);
lean_dec(v_cfg_1700_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 7, v_val_1699_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_leanOptions_1702_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_moreLeanArgs_1703_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_weakLeanArgs_1704_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_moreLeancArgs_1705_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_moreServerOptions_1706_);
lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_weakLeancArgs_1707_);
lean_ctor_set(v_reuseFailAlloc_1723_, 6, v_moreLinkObjs_1708_);
lean_ctor_set(v_reuseFailAlloc_1723_, 7, v_val_1699_);
lean_ctor_set(v_reuseFailAlloc_1723_, 8, v_moreLinkArgs_1709_);
lean_ctor_set(v_reuseFailAlloc_1723_, 9, v_weakLinkArgs_1710_);
lean_ctor_set(v_reuseFailAlloc_1723_, 10, v_platformIndependent_1712_);
lean_ctor_set(v_reuseFailAlloc_1723_, 11, v_dynlibs_1714_);
lean_ctor_set(v_reuseFailAlloc_1723_, 12, v_plugins_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13, v_buildType_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13 + 1, v_backend_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13 + 2, v_precompileImports_1713_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13 + 4, v_allowNonModules_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1726_, lean_object* v_cfg_1727_){
_start:
{
uint8_t v_buildType_1728_; lean_object* v_leanOptions_1729_; lean_object* v_moreLeanArgs_1730_; lean_object* v_weakLeanArgs_1731_; lean_object* v_moreLeancArgs_1732_; lean_object* v_moreServerOptions_1733_; lean_object* v_weakLeancArgs_1734_; lean_object* v_moreLinkObjs_1735_; lean_object* v_moreLinkLibs_1736_; lean_object* v_moreLinkArgs_1737_; lean_object* v_weakLinkArgs_1738_; uint8_t v_backend_1739_; lean_object* v_platformIndependent_1740_; uint8_t v_precompileImports_1741_; lean_object* v_dynlibs_1742_; lean_object* v_plugins_1743_; uint8_t v_requiresModuleSystem_1744_; uint8_t v_allowNonModules_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1753_; 
v_buildType_1728_ = lean_ctor_get_uint8(v_cfg_1727_, sizeof(void*)*13);
v_leanOptions_1729_ = lean_ctor_get(v_cfg_1727_, 0);
v_moreLeanArgs_1730_ = lean_ctor_get(v_cfg_1727_, 1);
v_weakLeanArgs_1731_ = lean_ctor_get(v_cfg_1727_, 2);
v_moreLeancArgs_1732_ = lean_ctor_get(v_cfg_1727_, 3);
v_moreServerOptions_1733_ = lean_ctor_get(v_cfg_1727_, 4);
v_weakLeancArgs_1734_ = lean_ctor_get(v_cfg_1727_, 5);
v_moreLinkObjs_1735_ = lean_ctor_get(v_cfg_1727_, 6);
v_moreLinkLibs_1736_ = lean_ctor_get(v_cfg_1727_, 7);
v_moreLinkArgs_1737_ = lean_ctor_get(v_cfg_1727_, 8);
v_weakLinkArgs_1738_ = lean_ctor_get(v_cfg_1727_, 9);
v_backend_1739_ = lean_ctor_get_uint8(v_cfg_1727_, sizeof(void*)*13 + 1);
v_platformIndependent_1740_ = lean_ctor_get(v_cfg_1727_, 10);
v_precompileImports_1741_ = lean_ctor_get_uint8(v_cfg_1727_, sizeof(void*)*13 + 2);
v_dynlibs_1742_ = lean_ctor_get(v_cfg_1727_, 11);
v_plugins_1743_ = lean_ctor_get(v_cfg_1727_, 12);
v_requiresModuleSystem_1744_ = lean_ctor_get_uint8(v_cfg_1727_, sizeof(void*)*13 + 3);
v_allowNonModules_1745_ = lean_ctor_get_uint8(v_cfg_1727_, sizeof(void*)*13 + 4);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_cfg_1727_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1747_ = v_cfg_1727_;
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_plugins_1743_);
lean_inc(v_dynlibs_1742_);
lean_inc(v_platformIndependent_1740_);
lean_inc(v_weakLinkArgs_1738_);
lean_inc(v_moreLinkArgs_1737_);
lean_inc(v_moreLinkLibs_1736_);
lean_inc(v_moreLinkObjs_1735_);
lean_inc(v_weakLeancArgs_1734_);
lean_inc(v_moreServerOptions_1733_);
lean_inc(v_moreLeancArgs_1732_);
lean_inc(v_weakLeanArgs_1731_);
lean_inc(v_moreLeanArgs_1730_);
lean_inc(v_leanOptions_1729_);
lean_dec(v_cfg_1727_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
v___x_1749_ = lean_apply_1(v_f_1726_, v_moreLinkLibs_1736_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 7, v___x_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_leanOptions_1729_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_moreLeanArgs_1730_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_weakLeanArgs_1731_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_moreLeancArgs_1732_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_moreServerOptions_1733_);
lean_ctor_set(v_reuseFailAlloc_1752_, 5, v_weakLeancArgs_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 6, v_moreLinkObjs_1735_);
lean_ctor_set(v_reuseFailAlloc_1752_, 7, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1752_, 8, v_moreLinkArgs_1737_);
lean_ctor_set(v_reuseFailAlloc_1752_, 9, v_weakLinkArgs_1738_);
lean_ctor_set(v_reuseFailAlloc_1752_, 10, v_platformIndependent_1740_);
lean_ctor_set(v_reuseFailAlloc_1752_, 11, v_dynlibs_1742_);
lean_ctor_set(v_reuseFailAlloc_1752_, 12, v_plugins_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1752_, sizeof(void*)*13, v_buildType_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1752_, sizeof(void*)*13 + 1, v_backend_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1752_, sizeof(void*)*13 + 2, v_precompileImports_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1752_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1744_);
lean_ctor_set_uint8(v_reuseFailAlloc_1752_, sizeof(void*)*13 + 4, v_allowNonModules_1745_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1764_){
_start:
{
lean_object* v_moreLinkArgs_1765_; 
v_moreLinkArgs_1765_ = lean_ctor_get(v_cfg_1764_, 8);
lean_inc_ref(v_moreLinkArgs_1765_);
return v_moreLinkArgs_1765_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1766_);
lean_dec_ref(v_cfg_1766_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1768_, lean_object* v_cfg_1769_){
_start:
{
uint8_t v_buildType_1770_; lean_object* v_leanOptions_1771_; lean_object* v_moreLeanArgs_1772_; lean_object* v_weakLeanArgs_1773_; lean_object* v_moreLeancArgs_1774_; lean_object* v_moreServerOptions_1775_; lean_object* v_weakLeancArgs_1776_; lean_object* v_moreLinkObjs_1777_; lean_object* v_moreLinkLibs_1778_; lean_object* v_weakLinkArgs_1779_; uint8_t v_backend_1780_; lean_object* v_platformIndependent_1781_; uint8_t v_precompileImports_1782_; lean_object* v_dynlibs_1783_; lean_object* v_plugins_1784_; uint8_t v_requiresModuleSystem_1785_; uint8_t v_allowNonModules_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_buildType_1770_ = lean_ctor_get_uint8(v_cfg_1769_, sizeof(void*)*13);
v_leanOptions_1771_ = lean_ctor_get(v_cfg_1769_, 0);
v_moreLeanArgs_1772_ = lean_ctor_get(v_cfg_1769_, 1);
v_weakLeanArgs_1773_ = lean_ctor_get(v_cfg_1769_, 2);
v_moreLeancArgs_1774_ = lean_ctor_get(v_cfg_1769_, 3);
v_moreServerOptions_1775_ = lean_ctor_get(v_cfg_1769_, 4);
v_weakLeancArgs_1776_ = lean_ctor_get(v_cfg_1769_, 5);
v_moreLinkObjs_1777_ = lean_ctor_get(v_cfg_1769_, 6);
v_moreLinkLibs_1778_ = lean_ctor_get(v_cfg_1769_, 7);
v_weakLinkArgs_1779_ = lean_ctor_get(v_cfg_1769_, 9);
v_backend_1780_ = lean_ctor_get_uint8(v_cfg_1769_, sizeof(void*)*13 + 1);
v_platformIndependent_1781_ = lean_ctor_get(v_cfg_1769_, 10);
v_precompileImports_1782_ = lean_ctor_get_uint8(v_cfg_1769_, sizeof(void*)*13 + 2);
v_dynlibs_1783_ = lean_ctor_get(v_cfg_1769_, 11);
v_plugins_1784_ = lean_ctor_get(v_cfg_1769_, 12);
v_requiresModuleSystem_1785_ = lean_ctor_get_uint8(v_cfg_1769_, sizeof(void*)*13 + 3);
v_allowNonModules_1786_ = lean_ctor_get_uint8(v_cfg_1769_, sizeof(void*)*13 + 4);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_cfg_1769_);
if (v_isSharedCheck_1793_ == 0)
{
lean_object* v_unused_1794_; 
v_unused_1794_ = lean_ctor_get(v_cfg_1769_, 8);
lean_dec(v_unused_1794_);
v___x_1788_ = v_cfg_1769_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_plugins_1784_);
lean_inc(v_dynlibs_1783_);
lean_inc(v_platformIndependent_1781_);
lean_inc(v_weakLinkArgs_1779_);
lean_inc(v_moreLinkLibs_1778_);
lean_inc(v_moreLinkObjs_1777_);
lean_inc(v_weakLeancArgs_1776_);
lean_inc(v_moreServerOptions_1775_);
lean_inc(v_moreLeancArgs_1774_);
lean_inc(v_weakLeanArgs_1773_);
lean_inc(v_moreLeanArgs_1772_);
lean_inc(v_leanOptions_1771_);
lean_dec(v_cfg_1769_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 8, v_val_1768_);
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_leanOptions_1771_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_moreLeanArgs_1772_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_weakLeanArgs_1773_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_moreLeancArgs_1774_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_moreServerOptions_1775_);
lean_ctor_set(v_reuseFailAlloc_1792_, 5, v_weakLeancArgs_1776_);
lean_ctor_set(v_reuseFailAlloc_1792_, 6, v_moreLinkObjs_1777_);
lean_ctor_set(v_reuseFailAlloc_1792_, 7, v_moreLinkLibs_1778_);
lean_ctor_set(v_reuseFailAlloc_1792_, 8, v_val_1768_);
lean_ctor_set(v_reuseFailAlloc_1792_, 9, v_weakLinkArgs_1779_);
lean_ctor_set(v_reuseFailAlloc_1792_, 10, v_platformIndependent_1781_);
lean_ctor_set(v_reuseFailAlloc_1792_, 11, v_dynlibs_1783_);
lean_ctor_set(v_reuseFailAlloc_1792_, 12, v_plugins_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*13, v_buildType_1770_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*13 + 1, v_backend_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*13 + 2, v_precompileImports_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*13 + 4, v_allowNonModules_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1795_, lean_object* v_cfg_1796_){
_start:
{
uint8_t v_buildType_1797_; lean_object* v_leanOptions_1798_; lean_object* v_moreLeanArgs_1799_; lean_object* v_weakLeanArgs_1800_; lean_object* v_moreLeancArgs_1801_; lean_object* v_moreServerOptions_1802_; lean_object* v_weakLeancArgs_1803_; lean_object* v_moreLinkObjs_1804_; lean_object* v_moreLinkLibs_1805_; lean_object* v_moreLinkArgs_1806_; lean_object* v_weakLinkArgs_1807_; uint8_t v_backend_1808_; lean_object* v_platformIndependent_1809_; uint8_t v_precompileImports_1810_; lean_object* v_dynlibs_1811_; lean_object* v_plugins_1812_; uint8_t v_requiresModuleSystem_1813_; uint8_t v_allowNonModules_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1822_; 
v_buildType_1797_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*13);
v_leanOptions_1798_ = lean_ctor_get(v_cfg_1796_, 0);
v_moreLeanArgs_1799_ = lean_ctor_get(v_cfg_1796_, 1);
v_weakLeanArgs_1800_ = lean_ctor_get(v_cfg_1796_, 2);
v_moreLeancArgs_1801_ = lean_ctor_get(v_cfg_1796_, 3);
v_moreServerOptions_1802_ = lean_ctor_get(v_cfg_1796_, 4);
v_weakLeancArgs_1803_ = lean_ctor_get(v_cfg_1796_, 5);
v_moreLinkObjs_1804_ = lean_ctor_get(v_cfg_1796_, 6);
v_moreLinkLibs_1805_ = lean_ctor_get(v_cfg_1796_, 7);
v_moreLinkArgs_1806_ = lean_ctor_get(v_cfg_1796_, 8);
v_weakLinkArgs_1807_ = lean_ctor_get(v_cfg_1796_, 9);
v_backend_1808_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*13 + 1);
v_platformIndependent_1809_ = lean_ctor_get(v_cfg_1796_, 10);
v_precompileImports_1810_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*13 + 2);
v_dynlibs_1811_ = lean_ctor_get(v_cfg_1796_, 11);
v_plugins_1812_ = lean_ctor_get(v_cfg_1796_, 12);
v_requiresModuleSystem_1813_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*13 + 3);
v_allowNonModules_1814_ = lean_ctor_get_uint8(v_cfg_1796_, sizeof(void*)*13 + 4);
v_isSharedCheck_1822_ = !lean_is_exclusive(v_cfg_1796_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1816_ = v_cfg_1796_;
v_isShared_1817_ = v_isSharedCheck_1822_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_plugins_1812_);
lean_inc(v_dynlibs_1811_);
lean_inc(v_platformIndependent_1809_);
lean_inc(v_weakLinkArgs_1807_);
lean_inc(v_moreLinkArgs_1806_);
lean_inc(v_moreLinkLibs_1805_);
lean_inc(v_moreLinkObjs_1804_);
lean_inc(v_weakLeancArgs_1803_);
lean_inc(v_moreServerOptions_1802_);
lean_inc(v_moreLeancArgs_1801_);
lean_inc(v_weakLeanArgs_1800_);
lean_inc(v_moreLeanArgs_1799_);
lean_inc(v_leanOptions_1798_);
lean_dec(v_cfg_1796_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1822_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1820_; 
v___x_1818_ = lean_apply_1(v_f_1795_, v_moreLinkArgs_1806_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 8, v___x_1818_);
v___x_1820_ = v___x_1816_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_leanOptions_1798_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_moreLeanArgs_1799_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_weakLeanArgs_1800_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_moreLeancArgs_1801_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_moreServerOptions_1802_);
lean_ctor_set(v_reuseFailAlloc_1821_, 5, v_weakLeancArgs_1803_);
lean_ctor_set(v_reuseFailAlloc_1821_, 6, v_moreLinkObjs_1804_);
lean_ctor_set(v_reuseFailAlloc_1821_, 7, v_moreLinkLibs_1805_);
lean_ctor_set(v_reuseFailAlloc_1821_, 8, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1821_, 9, v_weakLinkArgs_1807_);
lean_ctor_set(v_reuseFailAlloc_1821_, 10, v_platformIndependent_1809_);
lean_ctor_set(v_reuseFailAlloc_1821_, 11, v_dynlibs_1811_);
lean_ctor_set(v_reuseFailAlloc_1821_, 12, v_plugins_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*13, v_buildType_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*13 + 1, v_backend_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*13 + 2, v_precompileImports_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1821_, sizeof(void*)*13 + 4, v_allowNonModules_1814_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1833_){
_start:
{
lean_object* v_weakLinkArgs_1834_; 
v_weakLinkArgs_1834_ = lean_ctor_get(v_cfg_1833_, 9);
lean_inc_ref(v_weakLinkArgs_1834_);
return v_weakLinkArgs_1834_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1835_);
lean_dec_ref(v_cfg_1835_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1837_, lean_object* v_cfg_1838_){
_start:
{
uint8_t v_buildType_1839_; lean_object* v_leanOptions_1840_; lean_object* v_moreLeanArgs_1841_; lean_object* v_weakLeanArgs_1842_; lean_object* v_moreLeancArgs_1843_; lean_object* v_moreServerOptions_1844_; lean_object* v_weakLeancArgs_1845_; lean_object* v_moreLinkObjs_1846_; lean_object* v_moreLinkLibs_1847_; lean_object* v_moreLinkArgs_1848_; uint8_t v_backend_1849_; lean_object* v_platformIndependent_1850_; uint8_t v_precompileImports_1851_; lean_object* v_dynlibs_1852_; lean_object* v_plugins_1853_; uint8_t v_requiresModuleSystem_1854_; uint8_t v_allowNonModules_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v_buildType_1839_ = lean_ctor_get_uint8(v_cfg_1838_, sizeof(void*)*13);
v_leanOptions_1840_ = lean_ctor_get(v_cfg_1838_, 0);
v_moreLeanArgs_1841_ = lean_ctor_get(v_cfg_1838_, 1);
v_weakLeanArgs_1842_ = lean_ctor_get(v_cfg_1838_, 2);
v_moreLeancArgs_1843_ = lean_ctor_get(v_cfg_1838_, 3);
v_moreServerOptions_1844_ = lean_ctor_get(v_cfg_1838_, 4);
v_weakLeancArgs_1845_ = lean_ctor_get(v_cfg_1838_, 5);
v_moreLinkObjs_1846_ = lean_ctor_get(v_cfg_1838_, 6);
v_moreLinkLibs_1847_ = lean_ctor_get(v_cfg_1838_, 7);
v_moreLinkArgs_1848_ = lean_ctor_get(v_cfg_1838_, 8);
v_backend_1849_ = lean_ctor_get_uint8(v_cfg_1838_, sizeof(void*)*13 + 1);
v_platformIndependent_1850_ = lean_ctor_get(v_cfg_1838_, 10);
v_precompileImports_1851_ = lean_ctor_get_uint8(v_cfg_1838_, sizeof(void*)*13 + 2);
v_dynlibs_1852_ = lean_ctor_get(v_cfg_1838_, 11);
v_plugins_1853_ = lean_ctor_get(v_cfg_1838_, 12);
v_requiresModuleSystem_1854_ = lean_ctor_get_uint8(v_cfg_1838_, sizeof(void*)*13 + 3);
v_allowNonModules_1855_ = lean_ctor_get_uint8(v_cfg_1838_, sizeof(void*)*13 + 4);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_cfg_1838_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; 
v_unused_1863_ = lean_ctor_get(v_cfg_1838_, 9);
lean_dec(v_unused_1863_);
v___x_1857_ = v_cfg_1838_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_plugins_1853_);
lean_inc(v_dynlibs_1852_);
lean_inc(v_platformIndependent_1850_);
lean_inc(v_moreLinkArgs_1848_);
lean_inc(v_moreLinkLibs_1847_);
lean_inc(v_moreLinkObjs_1846_);
lean_inc(v_weakLeancArgs_1845_);
lean_inc(v_moreServerOptions_1844_);
lean_inc(v_moreLeancArgs_1843_);
lean_inc(v_weakLeanArgs_1842_);
lean_inc(v_moreLeanArgs_1841_);
lean_inc(v_leanOptions_1840_);
lean_dec(v_cfg_1838_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 9, v_val_1837_);
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_leanOptions_1840_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_moreLeanArgs_1841_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_weakLeanArgs_1842_);
lean_ctor_set(v_reuseFailAlloc_1861_, 3, v_moreLeancArgs_1843_);
lean_ctor_set(v_reuseFailAlloc_1861_, 4, v_moreServerOptions_1844_);
lean_ctor_set(v_reuseFailAlloc_1861_, 5, v_weakLeancArgs_1845_);
lean_ctor_set(v_reuseFailAlloc_1861_, 6, v_moreLinkObjs_1846_);
lean_ctor_set(v_reuseFailAlloc_1861_, 7, v_moreLinkLibs_1847_);
lean_ctor_set(v_reuseFailAlloc_1861_, 8, v_moreLinkArgs_1848_);
lean_ctor_set(v_reuseFailAlloc_1861_, 9, v_val_1837_);
lean_ctor_set(v_reuseFailAlloc_1861_, 10, v_platformIndependent_1850_);
lean_ctor_set(v_reuseFailAlloc_1861_, 11, v_dynlibs_1852_);
lean_ctor_set(v_reuseFailAlloc_1861_, 12, v_plugins_1853_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*13, v_buildType_1839_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*13 + 1, v_backend_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*13 + 2, v_precompileImports_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1854_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*13 + 4, v_allowNonModules_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1864_, lean_object* v_cfg_1865_){
_start:
{
uint8_t v_buildType_1866_; lean_object* v_leanOptions_1867_; lean_object* v_moreLeanArgs_1868_; lean_object* v_weakLeanArgs_1869_; lean_object* v_moreLeancArgs_1870_; lean_object* v_moreServerOptions_1871_; lean_object* v_weakLeancArgs_1872_; lean_object* v_moreLinkObjs_1873_; lean_object* v_moreLinkLibs_1874_; lean_object* v_moreLinkArgs_1875_; lean_object* v_weakLinkArgs_1876_; uint8_t v_backend_1877_; lean_object* v_platformIndependent_1878_; uint8_t v_precompileImports_1879_; lean_object* v_dynlibs_1880_; lean_object* v_plugins_1881_; uint8_t v_requiresModuleSystem_1882_; uint8_t v_allowNonModules_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
v_buildType_1866_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13);
v_leanOptions_1867_ = lean_ctor_get(v_cfg_1865_, 0);
v_moreLeanArgs_1868_ = lean_ctor_get(v_cfg_1865_, 1);
v_weakLeanArgs_1869_ = lean_ctor_get(v_cfg_1865_, 2);
v_moreLeancArgs_1870_ = lean_ctor_get(v_cfg_1865_, 3);
v_moreServerOptions_1871_ = lean_ctor_get(v_cfg_1865_, 4);
v_weakLeancArgs_1872_ = lean_ctor_get(v_cfg_1865_, 5);
v_moreLinkObjs_1873_ = lean_ctor_get(v_cfg_1865_, 6);
v_moreLinkLibs_1874_ = lean_ctor_get(v_cfg_1865_, 7);
v_moreLinkArgs_1875_ = lean_ctor_get(v_cfg_1865_, 8);
v_weakLinkArgs_1876_ = lean_ctor_get(v_cfg_1865_, 9);
v_backend_1877_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13 + 1);
v_platformIndependent_1878_ = lean_ctor_get(v_cfg_1865_, 10);
v_precompileImports_1879_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13 + 2);
v_dynlibs_1880_ = lean_ctor_get(v_cfg_1865_, 11);
v_plugins_1881_ = lean_ctor_get(v_cfg_1865_, 12);
v_requiresModuleSystem_1882_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13 + 3);
v_allowNonModules_1883_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13 + 4);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_cfg_1865_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1885_ = v_cfg_1865_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_plugins_1881_);
lean_inc(v_dynlibs_1880_);
lean_inc(v_platformIndependent_1878_);
lean_inc(v_weakLinkArgs_1876_);
lean_inc(v_moreLinkArgs_1875_);
lean_inc(v_moreLinkLibs_1874_);
lean_inc(v_moreLinkObjs_1873_);
lean_inc(v_weakLeancArgs_1872_);
lean_inc(v_moreServerOptions_1871_);
lean_inc(v_moreLeancArgs_1870_);
lean_inc(v_weakLeanArgs_1869_);
lean_inc(v_moreLeanArgs_1868_);
lean_inc(v_leanOptions_1867_);
lean_dec(v_cfg_1865_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_apply_1(v_f_1864_, v_weakLinkArgs_1876_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 9, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_leanOptions_1867_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_moreLeanArgs_1868_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_weakLeanArgs_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_moreLeancArgs_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_moreServerOptions_1871_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_weakLeancArgs_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_moreLinkObjs_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_moreLinkLibs_1874_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_moreLinkArgs_1875_);
lean_ctor_set(v_reuseFailAlloc_1890_, 9, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1890_, 10, v_platformIndependent_1878_);
lean_ctor_set(v_reuseFailAlloc_1890_, 11, v_dynlibs_1880_);
lean_ctor_set(v_reuseFailAlloc_1890_, 12, v_plugins_1881_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13, v_buildType_1866_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 1, v_backend_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 2, v_precompileImports_1879_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1882_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13 + 4, v_allowNonModules_1883_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1902_){
_start:
{
uint8_t v_backend_1903_; 
v_backend_1903_ = lean_ctor_get_uint8(v_cfg_1902_, sizeof(void*)*13 + 1);
return v_backend_1903_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_backend___proj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_1902_ = stack[0].m_obj;
uint8_t v_res_1904_;
v_res_1904_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1902_);
stack->m_num = v_res_1904_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1905_){
_start:
{
uint8_t v_res_1906_; lean_object* v_r_1907_; 
v_res_1906_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1905_);
lean_dec_ref(v_cfg_1905_);
v_r_1907_ = lean_box(v_res_1906_);
return v_r_1907_;
}
}
lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1908_, lean_object* v_cfg_1909_){
_start:
{
uint8_t v_buildType_1910_; lean_object* v_leanOptions_1911_; lean_object* v_moreLeanArgs_1912_; lean_object* v_weakLeanArgs_1913_; lean_object* v_moreLeancArgs_1914_; lean_object* v_moreServerOptions_1915_; lean_object* v_weakLeancArgs_1916_; lean_object* v_moreLinkObjs_1917_; lean_object* v_moreLinkLibs_1918_; lean_object* v_moreLinkArgs_1919_; lean_object* v_weakLinkArgs_1920_; lean_object* v_platformIndependent_1921_; uint8_t v_precompileImports_1922_; lean_object* v_dynlibs_1923_; lean_object* v_plugins_1924_; uint8_t v_requiresModuleSystem_1925_; uint8_t v_allowNonModules_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
v_buildType_1910_ = lean_ctor_get_uint8(v_cfg_1909_, sizeof(void*)*13);
v_leanOptions_1911_ = lean_ctor_get(v_cfg_1909_, 0);
v_moreLeanArgs_1912_ = lean_ctor_get(v_cfg_1909_, 1);
v_weakLeanArgs_1913_ = lean_ctor_get(v_cfg_1909_, 2);
v_moreLeancArgs_1914_ = lean_ctor_get(v_cfg_1909_, 3);
v_moreServerOptions_1915_ = lean_ctor_get(v_cfg_1909_, 4);
v_weakLeancArgs_1916_ = lean_ctor_get(v_cfg_1909_, 5);
v_moreLinkObjs_1917_ = lean_ctor_get(v_cfg_1909_, 6);
v_moreLinkLibs_1918_ = lean_ctor_get(v_cfg_1909_, 7);
v_moreLinkArgs_1919_ = lean_ctor_get(v_cfg_1909_, 8);
v_weakLinkArgs_1920_ = lean_ctor_get(v_cfg_1909_, 9);
v_platformIndependent_1921_ = lean_ctor_get(v_cfg_1909_, 10);
v_precompileImports_1922_ = lean_ctor_get_uint8(v_cfg_1909_, sizeof(void*)*13 + 2);
v_dynlibs_1923_ = lean_ctor_get(v_cfg_1909_, 11);
v_plugins_1924_ = lean_ctor_get(v_cfg_1909_, 12);
v_requiresModuleSystem_1925_ = lean_ctor_get_uint8(v_cfg_1909_, sizeof(void*)*13 + 3);
v_allowNonModules_1926_ = lean_ctor_get_uint8(v_cfg_1909_, sizeof(void*)*13 + 4);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_cfg_1909_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v_cfg_1909_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_plugins_1924_);
lean_inc(v_dynlibs_1923_);
lean_inc(v_platformIndependent_1921_);
lean_inc(v_weakLinkArgs_1920_);
lean_inc(v_moreLinkArgs_1919_);
lean_inc(v_moreLinkLibs_1918_);
lean_inc(v_moreLinkObjs_1917_);
lean_inc(v_weakLeancArgs_1916_);
lean_inc(v_moreServerOptions_1915_);
lean_inc(v_moreLeancArgs_1914_);
lean_inc(v_weakLeanArgs_1913_);
lean_inc(v_moreLeanArgs_1912_);
lean_inc(v_leanOptions_1911_);
lean_dec(v_cfg_1909_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_leanOptions_1911_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_moreLeanArgs_1912_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_weakLeanArgs_1913_);
lean_ctor_set(v_reuseFailAlloc_1932_, 3, v_moreLeancArgs_1914_);
lean_ctor_set(v_reuseFailAlloc_1932_, 4, v_moreServerOptions_1915_);
lean_ctor_set(v_reuseFailAlloc_1932_, 5, v_weakLeancArgs_1916_);
lean_ctor_set(v_reuseFailAlloc_1932_, 6, v_moreLinkObjs_1917_);
lean_ctor_set(v_reuseFailAlloc_1932_, 7, v_moreLinkLibs_1918_);
lean_ctor_set(v_reuseFailAlloc_1932_, 8, v_moreLinkArgs_1919_);
lean_ctor_set(v_reuseFailAlloc_1932_, 9, v_weakLinkArgs_1920_);
lean_ctor_set(v_reuseFailAlloc_1932_, 10, v_platformIndependent_1921_);
lean_ctor_set(v_reuseFailAlloc_1932_, 11, v_dynlibs_1923_);
lean_ctor_set(v_reuseFailAlloc_1932_, 12, v_plugins_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1932_, sizeof(void*)*13, v_buildType_1910_);
lean_ctor_set_uint8(v_reuseFailAlloc_1932_, sizeof(void*)*13 + 2, v_precompileImports_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1932_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1932_, sizeof(void*)*13 + 4, v_allowNonModules_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*13 + 1, v_val_1908_);
return v___x_1931_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanConfig_backend___proj___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_1908_ = stack[0].m_num;
lean_object* v_cfg_1909_ = stack[1].m_obj;
lean_object* v_res_1934_;
v_res_1934_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_1908_, v_cfg_1909_);
stack->m_obj
 = v_res_1934_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1935_, lean_object* v_cfg_1936_){
_start:
{
uint8_t v_val_90__boxed_1937_; lean_object* v_res_1938_; 
v_val_90__boxed_1937_ = lean_unbox(v_val_1935_);
v_res_1938_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_90__boxed_1937_, v_cfg_1936_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1939_, lean_object* v_cfg_1940_){
_start:
{
uint8_t v_buildType_1941_; lean_object* v_leanOptions_1942_; lean_object* v_moreLeanArgs_1943_; lean_object* v_weakLeanArgs_1944_; lean_object* v_moreLeancArgs_1945_; lean_object* v_moreServerOptions_1946_; lean_object* v_weakLeancArgs_1947_; lean_object* v_moreLinkObjs_1948_; lean_object* v_moreLinkLibs_1949_; lean_object* v_moreLinkArgs_1950_; lean_object* v_weakLinkArgs_1951_; uint8_t v_backend_1952_; lean_object* v_platformIndependent_1953_; uint8_t v_precompileImports_1954_; lean_object* v_dynlibs_1955_; lean_object* v_plugins_1956_; uint8_t v_requiresModuleSystem_1957_; uint8_t v_allowNonModules_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1968_; 
v_buildType_1941_ = lean_ctor_get_uint8(v_cfg_1940_, sizeof(void*)*13);
v_leanOptions_1942_ = lean_ctor_get(v_cfg_1940_, 0);
v_moreLeanArgs_1943_ = lean_ctor_get(v_cfg_1940_, 1);
v_weakLeanArgs_1944_ = lean_ctor_get(v_cfg_1940_, 2);
v_moreLeancArgs_1945_ = lean_ctor_get(v_cfg_1940_, 3);
v_moreServerOptions_1946_ = lean_ctor_get(v_cfg_1940_, 4);
v_weakLeancArgs_1947_ = lean_ctor_get(v_cfg_1940_, 5);
v_moreLinkObjs_1948_ = lean_ctor_get(v_cfg_1940_, 6);
v_moreLinkLibs_1949_ = lean_ctor_get(v_cfg_1940_, 7);
v_moreLinkArgs_1950_ = lean_ctor_get(v_cfg_1940_, 8);
v_weakLinkArgs_1951_ = lean_ctor_get(v_cfg_1940_, 9);
v_backend_1952_ = lean_ctor_get_uint8(v_cfg_1940_, sizeof(void*)*13 + 1);
v_platformIndependent_1953_ = lean_ctor_get(v_cfg_1940_, 10);
v_precompileImports_1954_ = lean_ctor_get_uint8(v_cfg_1940_, sizeof(void*)*13 + 2);
v_dynlibs_1955_ = lean_ctor_get(v_cfg_1940_, 11);
v_plugins_1956_ = lean_ctor_get(v_cfg_1940_, 12);
v_requiresModuleSystem_1957_ = lean_ctor_get_uint8(v_cfg_1940_, sizeof(void*)*13 + 3);
v_allowNonModules_1958_ = lean_ctor_get_uint8(v_cfg_1940_, sizeof(void*)*13 + 4);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_cfg_1940_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1960_ = v_cfg_1940_;
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_plugins_1956_);
lean_inc(v_dynlibs_1955_);
lean_inc(v_platformIndependent_1953_);
lean_inc(v_weakLinkArgs_1951_);
lean_inc(v_moreLinkArgs_1950_);
lean_inc(v_moreLinkLibs_1949_);
lean_inc(v_moreLinkObjs_1948_);
lean_inc(v_weakLeancArgs_1947_);
lean_inc(v_moreServerOptions_1946_);
lean_inc(v_moreLeancArgs_1945_);
lean_inc(v_weakLeanArgs_1944_);
lean_inc(v_moreLeanArgs_1943_);
lean_inc(v_leanOptions_1942_);
lean_dec(v_cfg_1940_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1962_ = lean_box(v_backend_1952_);
v___x_1963_ = lean_apply_1(v_f_1939_, v___x_1962_);
if (v_isShared_1961_ == 0)
{
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_leanOptions_1942_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v_moreLeanArgs_1943_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v_weakLeanArgs_1944_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v_moreLeancArgs_1945_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v_moreServerOptions_1946_);
lean_ctor_set(v_reuseFailAlloc_1967_, 5, v_weakLeancArgs_1947_);
lean_ctor_set(v_reuseFailAlloc_1967_, 6, v_moreLinkObjs_1948_);
lean_ctor_set(v_reuseFailAlloc_1967_, 7, v_moreLinkLibs_1949_);
lean_ctor_set(v_reuseFailAlloc_1967_, 8, v_moreLinkArgs_1950_);
lean_ctor_set(v_reuseFailAlloc_1967_, 9, v_weakLinkArgs_1951_);
lean_ctor_set(v_reuseFailAlloc_1967_, 10, v_platformIndependent_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 11, v_dynlibs_1955_);
lean_ctor_set(v_reuseFailAlloc_1967_, 12, v_plugins_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1967_, sizeof(void*)*13, v_buildType_1941_);
v___x_1965_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
uint8_t v___x_1966_; 
v___x_1966_ = lean_unbox(v___x_1963_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*13 + 1, v___x_1966_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*13 + 2, v_precompileImports_1954_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1957_);
lean_ctor_set_uint8(v___x_1965_, sizeof(void*)*13 + 4, v_allowNonModules_1958_);
return v___x_1965_;
}
}
}
}
uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1969_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = 2;
return v___x_1970_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_backend___proj___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1969_ = stack[0].m_obj;
uint8_t v_res_1971_;
v_res_1971_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1969_);
stack->m_num = v_res_1971_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1972_){
_start:
{
uint8_t v_res_1973_; lean_object* v_r_1974_; 
v_res_1973_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1972_);
lean_dec_ref(v_x_1972_);
v_r_1974_ = lean_box(v_res_1973_);
return v_r_1974_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1986_){
_start:
{
lean_object* v_platformIndependent_1987_; 
v_platformIndependent_1987_ = lean_ctor_get(v_cfg_1986_, 10);
lean_inc(v_platformIndependent_1987_);
return v_platformIndependent_1987_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1988_);
lean_dec_ref(v_cfg_1988_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1990_, lean_object* v_cfg_1991_){
_start:
{
uint8_t v_buildType_1992_; lean_object* v_leanOptions_1993_; lean_object* v_moreLeanArgs_1994_; lean_object* v_weakLeanArgs_1995_; lean_object* v_moreLeancArgs_1996_; lean_object* v_moreServerOptions_1997_; lean_object* v_weakLeancArgs_1998_; lean_object* v_moreLinkObjs_1999_; lean_object* v_moreLinkLibs_2000_; lean_object* v_moreLinkArgs_2001_; lean_object* v_weakLinkArgs_2002_; uint8_t v_backend_2003_; uint8_t v_precompileImports_2004_; lean_object* v_dynlibs_2005_; lean_object* v_plugins_2006_; uint8_t v_requiresModuleSystem_2007_; uint8_t v_allowNonModules_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
v_buildType_1992_ = lean_ctor_get_uint8(v_cfg_1991_, sizeof(void*)*13);
v_leanOptions_1993_ = lean_ctor_get(v_cfg_1991_, 0);
v_moreLeanArgs_1994_ = lean_ctor_get(v_cfg_1991_, 1);
v_weakLeanArgs_1995_ = lean_ctor_get(v_cfg_1991_, 2);
v_moreLeancArgs_1996_ = lean_ctor_get(v_cfg_1991_, 3);
v_moreServerOptions_1997_ = lean_ctor_get(v_cfg_1991_, 4);
v_weakLeancArgs_1998_ = lean_ctor_get(v_cfg_1991_, 5);
v_moreLinkObjs_1999_ = lean_ctor_get(v_cfg_1991_, 6);
v_moreLinkLibs_2000_ = lean_ctor_get(v_cfg_1991_, 7);
v_moreLinkArgs_2001_ = lean_ctor_get(v_cfg_1991_, 8);
v_weakLinkArgs_2002_ = lean_ctor_get(v_cfg_1991_, 9);
v_backend_2003_ = lean_ctor_get_uint8(v_cfg_1991_, sizeof(void*)*13 + 1);
v_precompileImports_2004_ = lean_ctor_get_uint8(v_cfg_1991_, sizeof(void*)*13 + 2);
v_dynlibs_2005_ = lean_ctor_get(v_cfg_1991_, 11);
v_plugins_2006_ = lean_ctor_get(v_cfg_1991_, 12);
v_requiresModuleSystem_2007_ = lean_ctor_get_uint8(v_cfg_1991_, sizeof(void*)*13 + 3);
v_allowNonModules_2008_ = lean_ctor_get_uint8(v_cfg_1991_, sizeof(void*)*13 + 4);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_cfg_1991_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v_cfg_1991_, 10);
lean_dec(v_unused_2016_);
v___x_2010_ = v_cfg_1991_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_plugins_2006_);
lean_inc(v_dynlibs_2005_);
lean_inc(v_weakLinkArgs_2002_);
lean_inc(v_moreLinkArgs_2001_);
lean_inc(v_moreLinkLibs_2000_);
lean_inc(v_moreLinkObjs_1999_);
lean_inc(v_weakLeancArgs_1998_);
lean_inc(v_moreServerOptions_1997_);
lean_inc(v_moreLeancArgs_1996_);
lean_inc(v_weakLeanArgs_1995_);
lean_inc(v_moreLeanArgs_1994_);
lean_inc(v_leanOptions_1993_);
lean_dec(v_cfg_1991_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 10, v_val_1990_);
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_leanOptions_1993_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_moreLeanArgs_1994_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_weakLeanArgs_1995_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_moreLeancArgs_1996_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_moreServerOptions_1997_);
lean_ctor_set(v_reuseFailAlloc_2014_, 5, v_weakLeancArgs_1998_);
lean_ctor_set(v_reuseFailAlloc_2014_, 6, v_moreLinkObjs_1999_);
lean_ctor_set(v_reuseFailAlloc_2014_, 7, v_moreLinkLibs_2000_);
lean_ctor_set(v_reuseFailAlloc_2014_, 8, v_moreLinkArgs_2001_);
lean_ctor_set(v_reuseFailAlloc_2014_, 9, v_weakLinkArgs_2002_);
lean_ctor_set(v_reuseFailAlloc_2014_, 10, v_val_1990_);
lean_ctor_set(v_reuseFailAlloc_2014_, 11, v_dynlibs_2005_);
lean_ctor_set(v_reuseFailAlloc_2014_, 12, v_plugins_2006_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13, v_buildType_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 1, v_backend_2003_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 2, v_precompileImports_2004_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2014_, sizeof(void*)*13 + 4, v_allowNonModules_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_2017_, lean_object* v_cfg_2018_){
_start:
{
uint8_t v_buildType_2019_; lean_object* v_leanOptions_2020_; lean_object* v_moreLeanArgs_2021_; lean_object* v_weakLeanArgs_2022_; lean_object* v_moreLeancArgs_2023_; lean_object* v_moreServerOptions_2024_; lean_object* v_weakLeancArgs_2025_; lean_object* v_moreLinkObjs_2026_; lean_object* v_moreLinkLibs_2027_; lean_object* v_moreLinkArgs_2028_; lean_object* v_weakLinkArgs_2029_; uint8_t v_backend_2030_; lean_object* v_platformIndependent_2031_; uint8_t v_precompileImports_2032_; lean_object* v_dynlibs_2033_; lean_object* v_plugins_2034_; uint8_t v_requiresModuleSystem_2035_; uint8_t v_allowNonModules_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
v_buildType_2019_ = lean_ctor_get_uint8(v_cfg_2018_, sizeof(void*)*13);
v_leanOptions_2020_ = lean_ctor_get(v_cfg_2018_, 0);
v_moreLeanArgs_2021_ = lean_ctor_get(v_cfg_2018_, 1);
v_weakLeanArgs_2022_ = lean_ctor_get(v_cfg_2018_, 2);
v_moreLeancArgs_2023_ = lean_ctor_get(v_cfg_2018_, 3);
v_moreServerOptions_2024_ = lean_ctor_get(v_cfg_2018_, 4);
v_weakLeancArgs_2025_ = lean_ctor_get(v_cfg_2018_, 5);
v_moreLinkObjs_2026_ = lean_ctor_get(v_cfg_2018_, 6);
v_moreLinkLibs_2027_ = lean_ctor_get(v_cfg_2018_, 7);
v_moreLinkArgs_2028_ = lean_ctor_get(v_cfg_2018_, 8);
v_weakLinkArgs_2029_ = lean_ctor_get(v_cfg_2018_, 9);
v_backend_2030_ = lean_ctor_get_uint8(v_cfg_2018_, sizeof(void*)*13 + 1);
v_platformIndependent_2031_ = lean_ctor_get(v_cfg_2018_, 10);
v_precompileImports_2032_ = lean_ctor_get_uint8(v_cfg_2018_, sizeof(void*)*13 + 2);
v_dynlibs_2033_ = lean_ctor_get(v_cfg_2018_, 11);
v_plugins_2034_ = lean_ctor_get(v_cfg_2018_, 12);
v_requiresModuleSystem_2035_ = lean_ctor_get_uint8(v_cfg_2018_, sizeof(void*)*13 + 3);
v_allowNonModules_2036_ = lean_ctor_get_uint8(v_cfg_2018_, sizeof(void*)*13 + 4);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_cfg_2018_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2038_ = v_cfg_2018_;
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_plugins_2034_);
lean_inc(v_dynlibs_2033_);
lean_inc(v_platformIndependent_2031_);
lean_inc(v_weakLinkArgs_2029_);
lean_inc(v_moreLinkArgs_2028_);
lean_inc(v_moreLinkLibs_2027_);
lean_inc(v_moreLinkObjs_2026_);
lean_inc(v_weakLeancArgs_2025_);
lean_inc(v_moreServerOptions_2024_);
lean_inc(v_moreLeancArgs_2023_);
lean_inc(v_weakLeanArgs_2022_);
lean_inc(v_moreLeanArgs_2021_);
lean_inc(v_leanOptions_2020_);
lean_dec(v_cfg_2018_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2044_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2040_ = lean_apply_1(v_f_2017_, v_platformIndependent_2031_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 10, v___x_2040_);
v___x_2042_ = v___x_2038_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_leanOptions_2020_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_moreLeanArgs_2021_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_weakLeanArgs_2022_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_moreLeancArgs_2023_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v_moreServerOptions_2024_);
lean_ctor_set(v_reuseFailAlloc_2043_, 5, v_weakLeancArgs_2025_);
lean_ctor_set(v_reuseFailAlloc_2043_, 6, v_moreLinkObjs_2026_);
lean_ctor_set(v_reuseFailAlloc_2043_, 7, v_moreLinkLibs_2027_);
lean_ctor_set(v_reuseFailAlloc_2043_, 8, v_moreLinkArgs_2028_);
lean_ctor_set(v_reuseFailAlloc_2043_, 9, v_weakLinkArgs_2029_);
lean_ctor_set(v_reuseFailAlloc_2043_, 10, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2043_, 11, v_dynlibs_2033_);
lean_ctor_set(v_reuseFailAlloc_2043_, 12, v_plugins_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2043_, sizeof(void*)*13, v_buildType_2019_);
lean_ctor_set_uint8(v_reuseFailAlloc_2043_, sizeof(void*)*13 + 1, v_backend_2030_);
lean_ctor_set_uint8(v_reuseFailAlloc_2043_, sizeof(void*)*13 + 2, v_precompileImports_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2043_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2035_);
lean_ctor_set_uint8(v_reuseFailAlloc_2043_, sizeof(void*)*13 + 4, v_allowNonModules_2036_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = lean_box(0);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_2047_);
lean_dec_ref(v_x_2047_);
return v_res_2048_;
}
}
uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__0(lean_object* v_cfg_2060_){
_start:
{
uint8_t v_precompileImports_2061_; 
v_precompileImports_2061_ = lean_ctor_get_uint8(v_cfg_2060_, sizeof(void*)*13 + 2);
return v_precompileImports_2061_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_precompileImports___proj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2060_ = stack[0].m_obj;
uint8_t v_res_2062_;
v_res_2062_ = l_Lake_LeanConfig_precompileImports___proj___lam__0(v_cfg_2060_);
stack->m_num = v_res_2062_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__0___boxed(lean_object* v_cfg_2063_){
_start:
{
uint8_t v_res_2064_; lean_object* v_r_2065_; 
v_res_2064_ = l_Lake_LeanConfig_precompileImports___proj___lam__0(v_cfg_2063_);
lean_dec_ref(v_cfg_2063_);
v_r_2065_ = lean_box(v_res_2064_);
return v_r_2065_;
}
}
lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1(uint8_t v_val_2066_, lean_object* v_cfg_2067_){
_start:
{
uint8_t v_buildType_2068_; lean_object* v_leanOptions_2069_; lean_object* v_moreLeanArgs_2070_; lean_object* v_weakLeanArgs_2071_; lean_object* v_moreLeancArgs_2072_; lean_object* v_moreServerOptions_2073_; lean_object* v_weakLeancArgs_2074_; lean_object* v_moreLinkObjs_2075_; lean_object* v_moreLinkLibs_2076_; lean_object* v_moreLinkArgs_2077_; lean_object* v_weakLinkArgs_2078_; uint8_t v_backend_2079_; lean_object* v_platformIndependent_2080_; lean_object* v_dynlibs_2081_; lean_object* v_plugins_2082_; uint8_t v_requiresModuleSystem_2083_; uint8_t v_allowNonModules_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
v_buildType_2068_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*13);
v_leanOptions_2069_ = lean_ctor_get(v_cfg_2067_, 0);
v_moreLeanArgs_2070_ = lean_ctor_get(v_cfg_2067_, 1);
v_weakLeanArgs_2071_ = lean_ctor_get(v_cfg_2067_, 2);
v_moreLeancArgs_2072_ = lean_ctor_get(v_cfg_2067_, 3);
v_moreServerOptions_2073_ = lean_ctor_get(v_cfg_2067_, 4);
v_weakLeancArgs_2074_ = lean_ctor_get(v_cfg_2067_, 5);
v_moreLinkObjs_2075_ = lean_ctor_get(v_cfg_2067_, 6);
v_moreLinkLibs_2076_ = lean_ctor_get(v_cfg_2067_, 7);
v_moreLinkArgs_2077_ = lean_ctor_get(v_cfg_2067_, 8);
v_weakLinkArgs_2078_ = lean_ctor_get(v_cfg_2067_, 9);
v_backend_2079_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*13 + 1);
v_platformIndependent_2080_ = lean_ctor_get(v_cfg_2067_, 10);
v_dynlibs_2081_ = lean_ctor_get(v_cfg_2067_, 11);
v_plugins_2082_ = lean_ctor_get(v_cfg_2067_, 12);
v_requiresModuleSystem_2083_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*13 + 3);
v_allowNonModules_2084_ = lean_ctor_get_uint8(v_cfg_2067_, sizeof(void*)*13 + 4);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_cfg_2067_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v_cfg_2067_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_plugins_2082_);
lean_inc(v_dynlibs_2081_);
lean_inc(v_platformIndependent_2080_);
lean_inc(v_weakLinkArgs_2078_);
lean_inc(v_moreLinkArgs_2077_);
lean_inc(v_moreLinkLibs_2076_);
lean_inc(v_moreLinkObjs_2075_);
lean_inc(v_weakLeancArgs_2074_);
lean_inc(v_moreServerOptions_2073_);
lean_inc(v_moreLeancArgs_2072_);
lean_inc(v_weakLeanArgs_2071_);
lean_inc(v_moreLeanArgs_2070_);
lean_inc(v_leanOptions_2069_);
lean_dec(v_cfg_2067_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_leanOptions_2069_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_moreLeanArgs_2070_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_weakLeanArgs_2071_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_moreLeancArgs_2072_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v_moreServerOptions_2073_);
lean_ctor_set(v_reuseFailAlloc_2090_, 5, v_weakLeancArgs_2074_);
lean_ctor_set(v_reuseFailAlloc_2090_, 6, v_moreLinkObjs_2075_);
lean_ctor_set(v_reuseFailAlloc_2090_, 7, v_moreLinkLibs_2076_);
lean_ctor_set(v_reuseFailAlloc_2090_, 8, v_moreLinkArgs_2077_);
lean_ctor_set(v_reuseFailAlloc_2090_, 9, v_weakLinkArgs_2078_);
lean_ctor_set(v_reuseFailAlloc_2090_, 10, v_platformIndependent_2080_);
lean_ctor_set(v_reuseFailAlloc_2090_, 11, v_dynlibs_2081_);
lean_ctor_set(v_reuseFailAlloc_2090_, 12, v_plugins_2082_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*13, v_buildType_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*13 + 1, v_backend_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2083_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*13 + 4, v_allowNonModules_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*13 + 2, v_val_2066_);
return v___x_2089_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanConfig_precompileImports___proj___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_2066_ = stack[0].m_num;
lean_object* v_cfg_2067_ = stack[1].m_obj;
lean_object* v_res_2092_;
v_res_2092_ = l_Lake_LeanConfig_precompileImports___proj___lam__1(v_val_2066_, v_cfg_2067_);
stack->m_obj
 = v_res_2092_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1___boxed(lean_object* v_val_2093_, lean_object* v_cfg_2094_){
_start:
{
uint8_t v_val_90__boxed_2095_; lean_object* v_res_2096_; 
v_val_90__boxed_2095_ = lean_unbox(v_val_2093_);
v_res_2096_ = l_Lake_LeanConfig_precompileImports___proj___lam__1(v_val_90__boxed_2095_, v_cfg_2094_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__2(lean_object* v_f_2097_, lean_object* v_cfg_2098_){
_start:
{
uint8_t v_buildType_2099_; lean_object* v_leanOptions_2100_; lean_object* v_moreLeanArgs_2101_; lean_object* v_weakLeanArgs_2102_; lean_object* v_moreLeancArgs_2103_; lean_object* v_moreServerOptions_2104_; lean_object* v_weakLeancArgs_2105_; lean_object* v_moreLinkObjs_2106_; lean_object* v_moreLinkLibs_2107_; lean_object* v_moreLinkArgs_2108_; lean_object* v_weakLinkArgs_2109_; uint8_t v_backend_2110_; lean_object* v_platformIndependent_2111_; uint8_t v_precompileImports_2112_; lean_object* v_dynlibs_2113_; lean_object* v_plugins_2114_; uint8_t v_requiresModuleSystem_2115_; uint8_t v_allowNonModules_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2126_; 
v_buildType_2099_ = lean_ctor_get_uint8(v_cfg_2098_, sizeof(void*)*13);
v_leanOptions_2100_ = lean_ctor_get(v_cfg_2098_, 0);
v_moreLeanArgs_2101_ = lean_ctor_get(v_cfg_2098_, 1);
v_weakLeanArgs_2102_ = lean_ctor_get(v_cfg_2098_, 2);
v_moreLeancArgs_2103_ = lean_ctor_get(v_cfg_2098_, 3);
v_moreServerOptions_2104_ = lean_ctor_get(v_cfg_2098_, 4);
v_weakLeancArgs_2105_ = lean_ctor_get(v_cfg_2098_, 5);
v_moreLinkObjs_2106_ = lean_ctor_get(v_cfg_2098_, 6);
v_moreLinkLibs_2107_ = lean_ctor_get(v_cfg_2098_, 7);
v_moreLinkArgs_2108_ = lean_ctor_get(v_cfg_2098_, 8);
v_weakLinkArgs_2109_ = lean_ctor_get(v_cfg_2098_, 9);
v_backend_2110_ = lean_ctor_get_uint8(v_cfg_2098_, sizeof(void*)*13 + 1);
v_platformIndependent_2111_ = lean_ctor_get(v_cfg_2098_, 10);
v_precompileImports_2112_ = lean_ctor_get_uint8(v_cfg_2098_, sizeof(void*)*13 + 2);
v_dynlibs_2113_ = lean_ctor_get(v_cfg_2098_, 11);
v_plugins_2114_ = lean_ctor_get(v_cfg_2098_, 12);
v_requiresModuleSystem_2115_ = lean_ctor_get_uint8(v_cfg_2098_, sizeof(void*)*13 + 3);
v_allowNonModules_2116_ = lean_ctor_get_uint8(v_cfg_2098_, sizeof(void*)*13 + 4);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_cfg_2098_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2118_ = v_cfg_2098_;
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_plugins_2114_);
lean_inc(v_dynlibs_2113_);
lean_inc(v_platformIndependent_2111_);
lean_inc(v_weakLinkArgs_2109_);
lean_inc(v_moreLinkArgs_2108_);
lean_inc(v_moreLinkLibs_2107_);
lean_inc(v_moreLinkObjs_2106_);
lean_inc(v_weakLeancArgs_2105_);
lean_inc(v_moreServerOptions_2104_);
lean_inc(v_moreLeancArgs_2103_);
lean_inc(v_weakLeanArgs_2102_);
lean_inc(v_moreLeanArgs_2101_);
lean_inc(v_leanOptions_2100_);
lean_dec(v_cfg_2098_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2126_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2120_ = lean_box(v_precompileImports_2112_);
v___x_2121_ = lean_apply_1(v_f_2097_, v___x_2120_);
if (v_isShared_2119_ == 0)
{
v___x_2123_ = v___x_2118_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_leanOptions_2100_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_moreLeanArgs_2101_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v_weakLeanArgs_2102_);
lean_ctor_set(v_reuseFailAlloc_2125_, 3, v_moreLeancArgs_2103_);
lean_ctor_set(v_reuseFailAlloc_2125_, 4, v_moreServerOptions_2104_);
lean_ctor_set(v_reuseFailAlloc_2125_, 5, v_weakLeancArgs_2105_);
lean_ctor_set(v_reuseFailAlloc_2125_, 6, v_moreLinkObjs_2106_);
lean_ctor_set(v_reuseFailAlloc_2125_, 7, v_moreLinkLibs_2107_);
lean_ctor_set(v_reuseFailAlloc_2125_, 8, v_moreLinkArgs_2108_);
lean_ctor_set(v_reuseFailAlloc_2125_, 9, v_weakLinkArgs_2109_);
lean_ctor_set(v_reuseFailAlloc_2125_, 10, v_platformIndependent_2111_);
lean_ctor_set(v_reuseFailAlloc_2125_, 11, v_dynlibs_2113_);
lean_ctor_set(v_reuseFailAlloc_2125_, 12, v_plugins_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*13, v_buildType_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2125_, sizeof(void*)*13 + 1, v_backend_2110_);
v___x_2123_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_unbox(v___x_2121_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*13 + 2, v___x_2124_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2115_);
lean_ctor_set_uint8(v___x_2123_, sizeof(void*)*13 + 4, v_allowNonModules_2116_);
return v___x_2123_;
}
}
}
}
uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__3(lean_object* v_x_2127_){
_start:
{
uint8_t v___x_2128_; 
v___x_2128_ = 0;
return v___x_2128_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_precompileImports___proj___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2127_ = stack[0].m_obj;
uint8_t v_res_2129_;
v_res_2129_ = l_Lake_LeanConfig_precompileImports___proj___lam__3(v_x_2127_);
stack->m_num = v_res_2129_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__3___boxed(lean_object* v_x_2130_){
_start:
{
uint8_t v_res_2131_; lean_object* v_r_2132_; 
v_res_2131_ = l_Lake_LeanConfig_precompileImports___proj___lam__3(v_x_2130_);
lean_dec_ref(v_x_2130_);
v_r_2132_ = lean_box(v_res_2131_);
return v_r_2132_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_2144_){
_start:
{
lean_object* v_dynlibs_2145_; 
v_dynlibs_2145_ = lean_ctor_get(v_cfg_2144_, 11);
lean_inc_ref(v_dynlibs_2145_);
return v_dynlibs_2145_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_2146_);
lean_dec_ref(v_cfg_2146_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_2148_, lean_object* v_cfg_2149_){
_start:
{
uint8_t v_buildType_2150_; lean_object* v_leanOptions_2151_; lean_object* v_moreLeanArgs_2152_; lean_object* v_weakLeanArgs_2153_; lean_object* v_moreLeancArgs_2154_; lean_object* v_moreServerOptions_2155_; lean_object* v_weakLeancArgs_2156_; lean_object* v_moreLinkObjs_2157_; lean_object* v_moreLinkLibs_2158_; lean_object* v_moreLinkArgs_2159_; lean_object* v_weakLinkArgs_2160_; uint8_t v_backend_2161_; lean_object* v_platformIndependent_2162_; uint8_t v_precompileImports_2163_; lean_object* v_plugins_2164_; uint8_t v_requiresModuleSystem_2165_; uint8_t v_allowNonModules_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
v_buildType_2150_ = lean_ctor_get_uint8(v_cfg_2149_, sizeof(void*)*13);
v_leanOptions_2151_ = lean_ctor_get(v_cfg_2149_, 0);
v_moreLeanArgs_2152_ = lean_ctor_get(v_cfg_2149_, 1);
v_weakLeanArgs_2153_ = lean_ctor_get(v_cfg_2149_, 2);
v_moreLeancArgs_2154_ = lean_ctor_get(v_cfg_2149_, 3);
v_moreServerOptions_2155_ = lean_ctor_get(v_cfg_2149_, 4);
v_weakLeancArgs_2156_ = lean_ctor_get(v_cfg_2149_, 5);
v_moreLinkObjs_2157_ = lean_ctor_get(v_cfg_2149_, 6);
v_moreLinkLibs_2158_ = lean_ctor_get(v_cfg_2149_, 7);
v_moreLinkArgs_2159_ = lean_ctor_get(v_cfg_2149_, 8);
v_weakLinkArgs_2160_ = lean_ctor_get(v_cfg_2149_, 9);
v_backend_2161_ = lean_ctor_get_uint8(v_cfg_2149_, sizeof(void*)*13 + 1);
v_platformIndependent_2162_ = lean_ctor_get(v_cfg_2149_, 10);
v_precompileImports_2163_ = lean_ctor_get_uint8(v_cfg_2149_, sizeof(void*)*13 + 2);
v_plugins_2164_ = lean_ctor_get(v_cfg_2149_, 12);
v_requiresModuleSystem_2165_ = lean_ctor_get_uint8(v_cfg_2149_, sizeof(void*)*13 + 3);
v_allowNonModules_2166_ = lean_ctor_get_uint8(v_cfg_2149_, sizeof(void*)*13 + 4);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_cfg_2149_);
if (v_isSharedCheck_2173_ == 0)
{
lean_object* v_unused_2174_; 
v_unused_2174_ = lean_ctor_get(v_cfg_2149_, 11);
lean_dec(v_unused_2174_);
v___x_2168_ = v_cfg_2149_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_plugins_2164_);
lean_inc(v_platformIndependent_2162_);
lean_inc(v_weakLinkArgs_2160_);
lean_inc(v_moreLinkArgs_2159_);
lean_inc(v_moreLinkLibs_2158_);
lean_inc(v_moreLinkObjs_2157_);
lean_inc(v_weakLeancArgs_2156_);
lean_inc(v_moreServerOptions_2155_);
lean_inc(v_moreLeancArgs_2154_);
lean_inc(v_weakLeanArgs_2153_);
lean_inc(v_moreLeanArgs_2152_);
lean_inc(v_leanOptions_2151_);
lean_dec(v_cfg_2149_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 11, v_val_2148_);
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_leanOptions_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_moreLeanArgs_2152_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_weakLeanArgs_2153_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_moreLeancArgs_2154_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_moreServerOptions_2155_);
lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_weakLeancArgs_2156_);
lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_moreLinkObjs_2157_);
lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_moreLinkLibs_2158_);
lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_moreLinkArgs_2159_);
lean_ctor_set(v_reuseFailAlloc_2172_, 9, v_weakLinkArgs_2160_);
lean_ctor_set(v_reuseFailAlloc_2172_, 10, v_platformIndependent_2162_);
lean_ctor_set(v_reuseFailAlloc_2172_, 11, v_val_2148_);
lean_ctor_set(v_reuseFailAlloc_2172_, 12, v_plugins_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13, v_buildType_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 1, v_backend_2161_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 2, v_precompileImports_2163_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2172_, sizeof(void*)*13 + 4, v_allowNonModules_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_2175_, lean_object* v_cfg_2176_){
_start:
{
uint8_t v_buildType_2177_; lean_object* v_leanOptions_2178_; lean_object* v_moreLeanArgs_2179_; lean_object* v_weakLeanArgs_2180_; lean_object* v_moreLeancArgs_2181_; lean_object* v_moreServerOptions_2182_; lean_object* v_weakLeancArgs_2183_; lean_object* v_moreLinkObjs_2184_; lean_object* v_moreLinkLibs_2185_; lean_object* v_moreLinkArgs_2186_; lean_object* v_weakLinkArgs_2187_; uint8_t v_backend_2188_; lean_object* v_platformIndependent_2189_; uint8_t v_precompileImports_2190_; lean_object* v_dynlibs_2191_; lean_object* v_plugins_2192_; uint8_t v_requiresModuleSystem_2193_; uint8_t v_allowNonModules_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2202_; 
v_buildType_2177_ = lean_ctor_get_uint8(v_cfg_2176_, sizeof(void*)*13);
v_leanOptions_2178_ = lean_ctor_get(v_cfg_2176_, 0);
v_moreLeanArgs_2179_ = lean_ctor_get(v_cfg_2176_, 1);
v_weakLeanArgs_2180_ = lean_ctor_get(v_cfg_2176_, 2);
v_moreLeancArgs_2181_ = lean_ctor_get(v_cfg_2176_, 3);
v_moreServerOptions_2182_ = lean_ctor_get(v_cfg_2176_, 4);
v_weakLeancArgs_2183_ = lean_ctor_get(v_cfg_2176_, 5);
v_moreLinkObjs_2184_ = lean_ctor_get(v_cfg_2176_, 6);
v_moreLinkLibs_2185_ = lean_ctor_get(v_cfg_2176_, 7);
v_moreLinkArgs_2186_ = lean_ctor_get(v_cfg_2176_, 8);
v_weakLinkArgs_2187_ = lean_ctor_get(v_cfg_2176_, 9);
v_backend_2188_ = lean_ctor_get_uint8(v_cfg_2176_, sizeof(void*)*13 + 1);
v_platformIndependent_2189_ = lean_ctor_get(v_cfg_2176_, 10);
v_precompileImports_2190_ = lean_ctor_get_uint8(v_cfg_2176_, sizeof(void*)*13 + 2);
v_dynlibs_2191_ = lean_ctor_get(v_cfg_2176_, 11);
v_plugins_2192_ = lean_ctor_get(v_cfg_2176_, 12);
v_requiresModuleSystem_2193_ = lean_ctor_get_uint8(v_cfg_2176_, sizeof(void*)*13 + 3);
v_allowNonModules_2194_ = lean_ctor_get_uint8(v_cfg_2176_, sizeof(void*)*13 + 4);
v_isSharedCheck_2202_ = !lean_is_exclusive(v_cfg_2176_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2196_ = v_cfg_2176_;
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_plugins_2192_);
lean_inc(v_dynlibs_2191_);
lean_inc(v_platformIndependent_2189_);
lean_inc(v_weakLinkArgs_2187_);
lean_inc(v_moreLinkArgs_2186_);
lean_inc(v_moreLinkLibs_2185_);
lean_inc(v_moreLinkObjs_2184_);
lean_inc(v_weakLeancArgs_2183_);
lean_inc(v_moreServerOptions_2182_);
lean_inc(v_moreLeancArgs_2181_);
lean_inc(v_weakLeanArgs_2180_);
lean_inc(v_moreLeanArgs_2179_);
lean_inc(v_leanOptions_2178_);
lean_dec(v_cfg_2176_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_apply_1(v_f_2175_, v_dynlibs_2191_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 11, v___x_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_leanOptions_2178_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v_moreLeanArgs_2179_);
lean_ctor_set(v_reuseFailAlloc_2201_, 2, v_weakLeanArgs_2180_);
lean_ctor_set(v_reuseFailAlloc_2201_, 3, v_moreLeancArgs_2181_);
lean_ctor_set(v_reuseFailAlloc_2201_, 4, v_moreServerOptions_2182_);
lean_ctor_set(v_reuseFailAlloc_2201_, 5, v_weakLeancArgs_2183_);
lean_ctor_set(v_reuseFailAlloc_2201_, 6, v_moreLinkObjs_2184_);
lean_ctor_set(v_reuseFailAlloc_2201_, 7, v_moreLinkLibs_2185_);
lean_ctor_set(v_reuseFailAlloc_2201_, 8, v_moreLinkArgs_2186_);
lean_ctor_set(v_reuseFailAlloc_2201_, 9, v_weakLinkArgs_2187_);
lean_ctor_set(v_reuseFailAlloc_2201_, 10, v_platformIndependent_2189_);
lean_ctor_set(v_reuseFailAlloc_2201_, 11, v___x_2198_);
lean_ctor_set(v_reuseFailAlloc_2201_, 12, v_plugins_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2201_, sizeof(void*)*13, v_buildType_2177_);
lean_ctor_set_uint8(v_reuseFailAlloc_2201_, sizeof(void*)*13 + 1, v_backend_2188_);
lean_ctor_set_uint8(v_reuseFailAlloc_2201_, sizeof(void*)*13 + 2, v_precompileImports_2190_);
lean_ctor_set_uint8(v_reuseFailAlloc_2201_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2193_);
lean_ctor_set_uint8(v_reuseFailAlloc_2201_, sizeof(void*)*13 + 4, v_allowNonModules_2194_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_2213_){
_start:
{
lean_object* v_plugins_2214_; 
v_plugins_2214_ = lean_ctor_get(v_cfg_2213_, 12);
lean_inc_ref(v_plugins_2214_);
return v_plugins_2214_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_2215_);
lean_dec_ref(v_cfg_2215_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_2217_, lean_object* v_cfg_2218_){
_start:
{
uint8_t v_buildType_2219_; lean_object* v_leanOptions_2220_; lean_object* v_moreLeanArgs_2221_; lean_object* v_weakLeanArgs_2222_; lean_object* v_moreLeancArgs_2223_; lean_object* v_moreServerOptions_2224_; lean_object* v_weakLeancArgs_2225_; lean_object* v_moreLinkObjs_2226_; lean_object* v_moreLinkLibs_2227_; lean_object* v_moreLinkArgs_2228_; lean_object* v_weakLinkArgs_2229_; uint8_t v_backend_2230_; lean_object* v_platformIndependent_2231_; uint8_t v_precompileImports_2232_; lean_object* v_dynlibs_2233_; uint8_t v_requiresModuleSystem_2234_; uint8_t v_allowNonModules_2235_; lean_object* v___x_2237_; uint8_t v_isShared_2238_; uint8_t v_isSharedCheck_2242_; 
v_buildType_2219_ = lean_ctor_get_uint8(v_cfg_2218_, sizeof(void*)*13);
v_leanOptions_2220_ = lean_ctor_get(v_cfg_2218_, 0);
v_moreLeanArgs_2221_ = lean_ctor_get(v_cfg_2218_, 1);
v_weakLeanArgs_2222_ = lean_ctor_get(v_cfg_2218_, 2);
v_moreLeancArgs_2223_ = lean_ctor_get(v_cfg_2218_, 3);
v_moreServerOptions_2224_ = lean_ctor_get(v_cfg_2218_, 4);
v_weakLeancArgs_2225_ = lean_ctor_get(v_cfg_2218_, 5);
v_moreLinkObjs_2226_ = lean_ctor_get(v_cfg_2218_, 6);
v_moreLinkLibs_2227_ = lean_ctor_get(v_cfg_2218_, 7);
v_moreLinkArgs_2228_ = lean_ctor_get(v_cfg_2218_, 8);
v_weakLinkArgs_2229_ = lean_ctor_get(v_cfg_2218_, 9);
v_backend_2230_ = lean_ctor_get_uint8(v_cfg_2218_, sizeof(void*)*13 + 1);
v_platformIndependent_2231_ = lean_ctor_get(v_cfg_2218_, 10);
v_precompileImports_2232_ = lean_ctor_get_uint8(v_cfg_2218_, sizeof(void*)*13 + 2);
v_dynlibs_2233_ = lean_ctor_get(v_cfg_2218_, 11);
v_requiresModuleSystem_2234_ = lean_ctor_get_uint8(v_cfg_2218_, sizeof(void*)*13 + 3);
v_allowNonModules_2235_ = lean_ctor_get_uint8(v_cfg_2218_, sizeof(void*)*13 + 4);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_cfg_2218_);
if (v_isSharedCheck_2242_ == 0)
{
lean_object* v_unused_2243_; 
v_unused_2243_ = lean_ctor_get(v_cfg_2218_, 12);
lean_dec(v_unused_2243_);
v___x_2237_ = v_cfg_2218_;
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
else
{
lean_inc(v_dynlibs_2233_);
lean_inc(v_platformIndependent_2231_);
lean_inc(v_weakLinkArgs_2229_);
lean_inc(v_moreLinkArgs_2228_);
lean_inc(v_moreLinkLibs_2227_);
lean_inc(v_moreLinkObjs_2226_);
lean_inc(v_weakLeancArgs_2225_);
lean_inc(v_moreServerOptions_2224_);
lean_inc(v_moreLeancArgs_2223_);
lean_inc(v_weakLeanArgs_2222_);
lean_inc(v_moreLeanArgs_2221_);
lean_inc(v_leanOptions_2220_);
lean_dec(v_cfg_2218_);
v___x_2237_ = lean_box(0);
v_isShared_2238_ = v_isSharedCheck_2242_;
goto v_resetjp_2236_;
}
v_resetjp_2236_:
{
lean_object* v___x_2240_; 
if (v_isShared_2238_ == 0)
{
lean_ctor_set(v___x_2237_, 12, v_val_2217_);
v___x_2240_ = v___x_2237_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_leanOptions_2220_);
lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_moreLeanArgs_2221_);
lean_ctor_set(v_reuseFailAlloc_2241_, 2, v_weakLeanArgs_2222_);
lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_moreLeancArgs_2223_);
lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_moreServerOptions_2224_);
lean_ctor_set(v_reuseFailAlloc_2241_, 5, v_weakLeancArgs_2225_);
lean_ctor_set(v_reuseFailAlloc_2241_, 6, v_moreLinkObjs_2226_);
lean_ctor_set(v_reuseFailAlloc_2241_, 7, v_moreLinkLibs_2227_);
lean_ctor_set(v_reuseFailAlloc_2241_, 8, v_moreLinkArgs_2228_);
lean_ctor_set(v_reuseFailAlloc_2241_, 9, v_weakLinkArgs_2229_);
lean_ctor_set(v_reuseFailAlloc_2241_, 10, v_platformIndependent_2231_);
lean_ctor_set(v_reuseFailAlloc_2241_, 11, v_dynlibs_2233_);
lean_ctor_set(v_reuseFailAlloc_2241_, 12, v_val_2217_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*13, v_buildType_2219_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*13 + 1, v_backend_2230_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*13 + 2, v_precompileImports_2232_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2234_);
lean_ctor_set_uint8(v_reuseFailAlloc_2241_, sizeof(void*)*13 + 4, v_allowNonModules_2235_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_2244_, lean_object* v_cfg_2245_){
_start:
{
uint8_t v_buildType_2246_; lean_object* v_leanOptions_2247_; lean_object* v_moreLeanArgs_2248_; lean_object* v_weakLeanArgs_2249_; lean_object* v_moreLeancArgs_2250_; lean_object* v_moreServerOptions_2251_; lean_object* v_weakLeancArgs_2252_; lean_object* v_moreLinkObjs_2253_; lean_object* v_moreLinkLibs_2254_; lean_object* v_moreLinkArgs_2255_; lean_object* v_weakLinkArgs_2256_; uint8_t v_backend_2257_; lean_object* v_platformIndependent_2258_; uint8_t v_precompileImports_2259_; lean_object* v_dynlibs_2260_; lean_object* v_plugins_2261_; uint8_t v_requiresModuleSystem_2262_; uint8_t v_allowNonModules_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2271_; 
v_buildType_2246_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*13);
v_leanOptions_2247_ = lean_ctor_get(v_cfg_2245_, 0);
v_moreLeanArgs_2248_ = lean_ctor_get(v_cfg_2245_, 1);
v_weakLeanArgs_2249_ = lean_ctor_get(v_cfg_2245_, 2);
v_moreLeancArgs_2250_ = lean_ctor_get(v_cfg_2245_, 3);
v_moreServerOptions_2251_ = lean_ctor_get(v_cfg_2245_, 4);
v_weakLeancArgs_2252_ = lean_ctor_get(v_cfg_2245_, 5);
v_moreLinkObjs_2253_ = lean_ctor_get(v_cfg_2245_, 6);
v_moreLinkLibs_2254_ = lean_ctor_get(v_cfg_2245_, 7);
v_moreLinkArgs_2255_ = lean_ctor_get(v_cfg_2245_, 8);
v_weakLinkArgs_2256_ = lean_ctor_get(v_cfg_2245_, 9);
v_backend_2257_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*13 + 1);
v_platformIndependent_2258_ = lean_ctor_get(v_cfg_2245_, 10);
v_precompileImports_2259_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*13 + 2);
v_dynlibs_2260_ = lean_ctor_get(v_cfg_2245_, 11);
v_plugins_2261_ = lean_ctor_get(v_cfg_2245_, 12);
v_requiresModuleSystem_2262_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*13 + 3);
v_allowNonModules_2263_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*13 + 4);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_cfg_2245_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2265_ = v_cfg_2245_;
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_plugins_2261_);
lean_inc(v_dynlibs_2260_);
lean_inc(v_platformIndependent_2258_);
lean_inc(v_weakLinkArgs_2256_);
lean_inc(v_moreLinkArgs_2255_);
lean_inc(v_moreLinkLibs_2254_);
lean_inc(v_moreLinkObjs_2253_);
lean_inc(v_weakLeancArgs_2252_);
lean_inc(v_moreServerOptions_2251_);
lean_inc(v_moreLeancArgs_2250_);
lean_inc(v_weakLeanArgs_2249_);
lean_inc(v_moreLeanArgs_2248_);
lean_inc(v_leanOptions_2247_);
lean_dec(v_cfg_2245_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2271_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_apply_1(v_f_2244_, v_plugins_2261_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 12, v___x_2267_);
v___x_2269_ = v___x_2265_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_leanOptions_2247_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_moreLeanArgs_2248_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_weakLeanArgs_2249_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_moreLeancArgs_2250_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v_moreServerOptions_2251_);
lean_ctor_set(v_reuseFailAlloc_2270_, 5, v_weakLeancArgs_2252_);
lean_ctor_set(v_reuseFailAlloc_2270_, 6, v_moreLinkObjs_2253_);
lean_ctor_set(v_reuseFailAlloc_2270_, 7, v_moreLinkLibs_2254_);
lean_ctor_set(v_reuseFailAlloc_2270_, 8, v_moreLinkArgs_2255_);
lean_ctor_set(v_reuseFailAlloc_2270_, 9, v_weakLinkArgs_2256_);
lean_ctor_set(v_reuseFailAlloc_2270_, 10, v_platformIndependent_2258_);
lean_ctor_set(v_reuseFailAlloc_2270_, 11, v_dynlibs_2260_);
lean_ctor_set(v_reuseFailAlloc_2270_, 12, v___x_2267_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*13, v_buildType_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*13 + 1, v_backend_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*13 + 2, v_precompileImports_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2270_, sizeof(void*)*13 + 4, v_allowNonModules_2263_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object* v_cfg_2282_){
_start:
{
uint8_t v_requiresModuleSystem_2283_; 
v_requiresModuleSystem_2283_ = lean_ctor_get_uint8(v_cfg_2282_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_2283_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2282_ = stack[0].m_obj;
uint8_t v_res_2284_;
v_res_2284_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2282_);
stack->m_num = v_res_2284_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object* v_cfg_2285_){
_start:
{
uint8_t v_res_2286_; lean_object* v_r_2287_; 
v_res_2286_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2285_);
lean_dec_ref(v_cfg_2285_);
v_r_2287_ = lean_box(v_res_2286_);
return v_r_2287_;
}
}
lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t v_val_2288_, lean_object* v_cfg_2289_){
_start:
{
uint8_t v_buildType_2290_; lean_object* v_leanOptions_2291_; lean_object* v_moreLeanArgs_2292_; lean_object* v_weakLeanArgs_2293_; lean_object* v_moreLeancArgs_2294_; lean_object* v_moreServerOptions_2295_; lean_object* v_weakLeancArgs_2296_; lean_object* v_moreLinkObjs_2297_; lean_object* v_moreLinkLibs_2298_; lean_object* v_moreLinkArgs_2299_; lean_object* v_weakLinkArgs_2300_; uint8_t v_backend_2301_; lean_object* v_platformIndependent_2302_; uint8_t v_precompileImports_2303_; lean_object* v_dynlibs_2304_; lean_object* v_plugins_2305_; uint8_t v_allowNonModules_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
v_buildType_2290_ = lean_ctor_get_uint8(v_cfg_2289_, sizeof(void*)*13);
v_leanOptions_2291_ = lean_ctor_get(v_cfg_2289_, 0);
v_moreLeanArgs_2292_ = lean_ctor_get(v_cfg_2289_, 1);
v_weakLeanArgs_2293_ = lean_ctor_get(v_cfg_2289_, 2);
v_moreLeancArgs_2294_ = lean_ctor_get(v_cfg_2289_, 3);
v_moreServerOptions_2295_ = lean_ctor_get(v_cfg_2289_, 4);
v_weakLeancArgs_2296_ = lean_ctor_get(v_cfg_2289_, 5);
v_moreLinkObjs_2297_ = lean_ctor_get(v_cfg_2289_, 6);
v_moreLinkLibs_2298_ = lean_ctor_get(v_cfg_2289_, 7);
v_moreLinkArgs_2299_ = lean_ctor_get(v_cfg_2289_, 8);
v_weakLinkArgs_2300_ = lean_ctor_get(v_cfg_2289_, 9);
v_backend_2301_ = lean_ctor_get_uint8(v_cfg_2289_, sizeof(void*)*13 + 1);
v_platformIndependent_2302_ = lean_ctor_get(v_cfg_2289_, 10);
v_precompileImports_2303_ = lean_ctor_get_uint8(v_cfg_2289_, sizeof(void*)*13 + 2);
v_dynlibs_2304_ = lean_ctor_get(v_cfg_2289_, 11);
v_plugins_2305_ = lean_ctor_get(v_cfg_2289_, 12);
v_allowNonModules_2306_ = lean_ctor_get_uint8(v_cfg_2289_, sizeof(void*)*13 + 4);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_cfg_2289_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v_cfg_2289_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_plugins_2305_);
lean_inc(v_dynlibs_2304_);
lean_inc(v_platformIndependent_2302_);
lean_inc(v_weakLinkArgs_2300_);
lean_inc(v_moreLinkArgs_2299_);
lean_inc(v_moreLinkLibs_2298_);
lean_inc(v_moreLinkObjs_2297_);
lean_inc(v_weakLeancArgs_2296_);
lean_inc(v_moreServerOptions_2295_);
lean_inc(v_moreLeancArgs_2294_);
lean_inc(v_weakLeanArgs_2293_);
lean_inc(v_moreLeanArgs_2292_);
lean_inc(v_leanOptions_2291_);
lean_dec(v_cfg_2289_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_leanOptions_2291_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_moreLeanArgs_2292_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_weakLeanArgs_2293_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_moreLeancArgs_2294_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_moreServerOptions_2295_);
lean_ctor_set(v_reuseFailAlloc_2312_, 5, v_weakLeancArgs_2296_);
lean_ctor_set(v_reuseFailAlloc_2312_, 6, v_moreLinkObjs_2297_);
lean_ctor_set(v_reuseFailAlloc_2312_, 7, v_moreLinkLibs_2298_);
lean_ctor_set(v_reuseFailAlloc_2312_, 8, v_moreLinkArgs_2299_);
lean_ctor_set(v_reuseFailAlloc_2312_, 9, v_weakLinkArgs_2300_);
lean_ctor_set(v_reuseFailAlloc_2312_, 10, v_platformIndependent_2302_);
lean_ctor_set(v_reuseFailAlloc_2312_, 11, v_dynlibs_2304_);
lean_ctor_set(v_reuseFailAlloc_2312_, 12, v_plugins_2305_);
lean_ctor_set_uint8(v_reuseFailAlloc_2312_, sizeof(void*)*13, v_buildType_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2312_, sizeof(void*)*13 + 1, v_backend_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2312_, sizeof(void*)*13 + 2, v_precompileImports_2303_);
lean_ctor_set_uint8(v_reuseFailAlloc_2312_, sizeof(void*)*13 + 4, v_allowNonModules_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
lean_ctor_set_uint8(v___x_2311_, sizeof(void*)*13 + 3, v_val_2288_);
return v___x_2311_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_2288_ = stack[0].m_num;
lean_object* v_cfg_2289_ = stack[1].m_obj;
lean_object* v_res_2314_;
v_res_2314_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_2288_, v_cfg_2289_);
stack->m_obj
 = v_res_2314_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object* v_val_2315_, lean_object* v_cfg_2316_){
_start:
{
uint8_t v_val_90__boxed_2317_; lean_object* v_res_2318_; 
v_val_90__boxed_2317_ = lean_unbox(v_val_2315_);
v_res_2318_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_90__boxed_2317_, v_cfg_2316_);
return v_res_2318_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object* v_f_2319_, lean_object* v_cfg_2320_){
_start:
{
uint8_t v_buildType_2321_; lean_object* v_leanOptions_2322_; lean_object* v_moreLeanArgs_2323_; lean_object* v_weakLeanArgs_2324_; lean_object* v_moreLeancArgs_2325_; lean_object* v_moreServerOptions_2326_; lean_object* v_weakLeancArgs_2327_; lean_object* v_moreLinkObjs_2328_; lean_object* v_moreLinkLibs_2329_; lean_object* v_moreLinkArgs_2330_; lean_object* v_weakLinkArgs_2331_; uint8_t v_backend_2332_; lean_object* v_platformIndependent_2333_; uint8_t v_precompileImports_2334_; lean_object* v_dynlibs_2335_; lean_object* v_plugins_2336_; uint8_t v_requiresModuleSystem_2337_; uint8_t v_allowNonModules_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2348_; 
v_buildType_2321_ = lean_ctor_get_uint8(v_cfg_2320_, sizeof(void*)*13);
v_leanOptions_2322_ = lean_ctor_get(v_cfg_2320_, 0);
v_moreLeanArgs_2323_ = lean_ctor_get(v_cfg_2320_, 1);
v_weakLeanArgs_2324_ = lean_ctor_get(v_cfg_2320_, 2);
v_moreLeancArgs_2325_ = lean_ctor_get(v_cfg_2320_, 3);
v_moreServerOptions_2326_ = lean_ctor_get(v_cfg_2320_, 4);
v_weakLeancArgs_2327_ = lean_ctor_get(v_cfg_2320_, 5);
v_moreLinkObjs_2328_ = lean_ctor_get(v_cfg_2320_, 6);
v_moreLinkLibs_2329_ = lean_ctor_get(v_cfg_2320_, 7);
v_moreLinkArgs_2330_ = lean_ctor_get(v_cfg_2320_, 8);
v_weakLinkArgs_2331_ = lean_ctor_get(v_cfg_2320_, 9);
v_backend_2332_ = lean_ctor_get_uint8(v_cfg_2320_, sizeof(void*)*13 + 1);
v_platformIndependent_2333_ = lean_ctor_get(v_cfg_2320_, 10);
v_precompileImports_2334_ = lean_ctor_get_uint8(v_cfg_2320_, sizeof(void*)*13 + 2);
v_dynlibs_2335_ = lean_ctor_get(v_cfg_2320_, 11);
v_plugins_2336_ = lean_ctor_get(v_cfg_2320_, 12);
v_requiresModuleSystem_2337_ = lean_ctor_get_uint8(v_cfg_2320_, sizeof(void*)*13 + 3);
v_allowNonModules_2338_ = lean_ctor_get_uint8(v_cfg_2320_, sizeof(void*)*13 + 4);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_cfg_2320_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2340_ = v_cfg_2320_;
v_isShared_2341_ = v_isSharedCheck_2348_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_plugins_2336_);
lean_inc(v_dynlibs_2335_);
lean_inc(v_platformIndependent_2333_);
lean_inc(v_weakLinkArgs_2331_);
lean_inc(v_moreLinkArgs_2330_);
lean_inc(v_moreLinkLibs_2329_);
lean_inc(v_moreLinkObjs_2328_);
lean_inc(v_weakLeancArgs_2327_);
lean_inc(v_moreServerOptions_2326_);
lean_inc(v_moreLeancArgs_2325_);
lean_inc(v_weakLeanArgs_2324_);
lean_inc(v_moreLeanArgs_2323_);
lean_inc(v_leanOptions_2322_);
lean_dec(v_cfg_2320_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2348_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2345_; 
v___x_2342_ = lean_box(v_requiresModuleSystem_2337_);
v___x_2343_ = lean_apply_1(v_f_2319_, v___x_2342_);
if (v_isShared_2341_ == 0)
{
v___x_2345_ = v___x_2340_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_leanOptions_2322_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_moreLeanArgs_2323_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_weakLeanArgs_2324_);
lean_ctor_set(v_reuseFailAlloc_2347_, 3, v_moreLeancArgs_2325_);
lean_ctor_set(v_reuseFailAlloc_2347_, 4, v_moreServerOptions_2326_);
lean_ctor_set(v_reuseFailAlloc_2347_, 5, v_weakLeancArgs_2327_);
lean_ctor_set(v_reuseFailAlloc_2347_, 6, v_moreLinkObjs_2328_);
lean_ctor_set(v_reuseFailAlloc_2347_, 7, v_moreLinkLibs_2329_);
lean_ctor_set(v_reuseFailAlloc_2347_, 8, v_moreLinkArgs_2330_);
lean_ctor_set(v_reuseFailAlloc_2347_, 9, v_weakLinkArgs_2331_);
lean_ctor_set(v_reuseFailAlloc_2347_, 10, v_platformIndependent_2333_);
lean_ctor_set(v_reuseFailAlloc_2347_, 11, v_dynlibs_2335_);
lean_ctor_set(v_reuseFailAlloc_2347_, 12, v_plugins_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*13, v_buildType_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*13 + 1, v_backend_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*13 + 2, v_precompileImports_2334_);
v___x_2345_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
uint8_t v___x_2346_; 
v___x_2346_ = lean_unbox(v___x_2343_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*13 + 3, v___x_2346_);
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*13 + 4, v_allowNonModules_2338_);
return v___x_2345_;
}
}
}
}
uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object* v_cfg_2359_){
_start:
{
uint8_t v_allowNonModules_2360_; 
v_allowNonModules_2360_ = lean_ctor_get_uint8(v_cfg_2359_, sizeof(void*)*13 + 4);
return v_allowNonModules_2360_;
}
}
LEAN_EXPORT void l_Lake_LeanConfig_allowNonModules___proj___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cfg_2359_ = stack[0].m_obj;
uint8_t v_res_2361_;
v_res_2361_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2359_);
stack->m_num = v_res_2361_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object* v_cfg_2362_){
_start:
{
uint8_t v_res_2363_; lean_object* v_r_2364_; 
v_res_2363_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2362_);
lean_dec_ref(v_cfg_2362_);
v_r_2364_ = lean_box(v_res_2363_);
return v_r_2364_;
}
}
lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t v_val_2365_, lean_object* v_cfg_2366_){
_start:
{
uint8_t v_buildType_2367_; lean_object* v_leanOptions_2368_; lean_object* v_moreLeanArgs_2369_; lean_object* v_weakLeanArgs_2370_; lean_object* v_moreLeancArgs_2371_; lean_object* v_moreServerOptions_2372_; lean_object* v_weakLeancArgs_2373_; lean_object* v_moreLinkObjs_2374_; lean_object* v_moreLinkLibs_2375_; lean_object* v_moreLinkArgs_2376_; lean_object* v_weakLinkArgs_2377_; uint8_t v_backend_2378_; lean_object* v_platformIndependent_2379_; uint8_t v_precompileImports_2380_; lean_object* v_dynlibs_2381_; lean_object* v_plugins_2382_; uint8_t v_requiresModuleSystem_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
v_buildType_2367_ = lean_ctor_get_uint8(v_cfg_2366_, sizeof(void*)*13);
v_leanOptions_2368_ = lean_ctor_get(v_cfg_2366_, 0);
v_moreLeanArgs_2369_ = lean_ctor_get(v_cfg_2366_, 1);
v_weakLeanArgs_2370_ = lean_ctor_get(v_cfg_2366_, 2);
v_moreLeancArgs_2371_ = lean_ctor_get(v_cfg_2366_, 3);
v_moreServerOptions_2372_ = lean_ctor_get(v_cfg_2366_, 4);
v_weakLeancArgs_2373_ = lean_ctor_get(v_cfg_2366_, 5);
v_moreLinkObjs_2374_ = lean_ctor_get(v_cfg_2366_, 6);
v_moreLinkLibs_2375_ = lean_ctor_get(v_cfg_2366_, 7);
v_moreLinkArgs_2376_ = lean_ctor_get(v_cfg_2366_, 8);
v_weakLinkArgs_2377_ = lean_ctor_get(v_cfg_2366_, 9);
v_backend_2378_ = lean_ctor_get_uint8(v_cfg_2366_, sizeof(void*)*13 + 1);
v_platformIndependent_2379_ = lean_ctor_get(v_cfg_2366_, 10);
v_precompileImports_2380_ = lean_ctor_get_uint8(v_cfg_2366_, sizeof(void*)*13 + 2);
v_dynlibs_2381_ = lean_ctor_get(v_cfg_2366_, 11);
v_plugins_2382_ = lean_ctor_get(v_cfg_2366_, 12);
v_requiresModuleSystem_2383_ = lean_ctor_get_uint8(v_cfg_2366_, sizeof(void*)*13 + 3);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_cfg_2366_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v_cfg_2366_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_plugins_2382_);
lean_inc(v_dynlibs_2381_);
lean_inc(v_platformIndependent_2379_);
lean_inc(v_weakLinkArgs_2377_);
lean_inc(v_moreLinkArgs_2376_);
lean_inc(v_moreLinkLibs_2375_);
lean_inc(v_moreLinkObjs_2374_);
lean_inc(v_weakLeancArgs_2373_);
lean_inc(v_moreServerOptions_2372_);
lean_inc(v_moreLeancArgs_2371_);
lean_inc(v_weakLeanArgs_2370_);
lean_inc(v_moreLeanArgs_2369_);
lean_inc(v_leanOptions_2368_);
lean_dec(v_cfg_2366_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_leanOptions_2368_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_moreLeanArgs_2369_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_weakLeanArgs_2370_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v_moreLeancArgs_2371_);
lean_ctor_set(v_reuseFailAlloc_2389_, 4, v_moreServerOptions_2372_);
lean_ctor_set(v_reuseFailAlloc_2389_, 5, v_weakLeancArgs_2373_);
lean_ctor_set(v_reuseFailAlloc_2389_, 6, v_moreLinkObjs_2374_);
lean_ctor_set(v_reuseFailAlloc_2389_, 7, v_moreLinkLibs_2375_);
lean_ctor_set(v_reuseFailAlloc_2389_, 8, v_moreLinkArgs_2376_);
lean_ctor_set(v_reuseFailAlloc_2389_, 9, v_weakLinkArgs_2377_);
lean_ctor_set(v_reuseFailAlloc_2389_, 10, v_platformIndependent_2379_);
lean_ctor_set(v_reuseFailAlloc_2389_, 11, v_dynlibs_2381_);
lean_ctor_set(v_reuseFailAlloc_2389_, 12, v_plugins_2382_);
lean_ctor_set_uint8(v_reuseFailAlloc_2389_, sizeof(void*)*13, v_buildType_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2389_, sizeof(void*)*13 + 1, v_backend_2378_);
lean_ctor_set_uint8(v_reuseFailAlloc_2389_, sizeof(void*)*13 + 2, v_precompileImports_2380_);
lean_ctor_set_uint8(v_reuseFailAlloc_2389_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_ctor_set_uint8(v___x_2388_, sizeof(void*)*13 + 4, v_val_2365_);
return v___x_2388_;
}
}
}
}
LEAN_EXPORT void l_Lake_LeanConfig_allowNonModules___proj___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_2365_ = stack[0].m_num;
lean_object* v_cfg_2366_ = stack[1].m_obj;
lean_object* v_res_2391_;
v_res_2391_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_2365_, v_cfg_2366_);
stack->m_obj
 = v_res_2391_;
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object* v_val_2392_, lean_object* v_cfg_2393_){
_start:
{
uint8_t v_val_90__boxed_2394_; lean_object* v_res_2395_; 
v_val_90__boxed_2394_ = lean_unbox(v_val_2392_);
v_res_2395_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_90__boxed_2394_, v_cfg_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object* v_f_2396_, lean_object* v_cfg_2397_){
_start:
{
uint8_t v_buildType_2398_; lean_object* v_leanOptions_2399_; lean_object* v_moreLeanArgs_2400_; lean_object* v_weakLeanArgs_2401_; lean_object* v_moreLeancArgs_2402_; lean_object* v_moreServerOptions_2403_; lean_object* v_weakLeancArgs_2404_; lean_object* v_moreLinkObjs_2405_; lean_object* v_moreLinkLibs_2406_; lean_object* v_moreLinkArgs_2407_; lean_object* v_weakLinkArgs_2408_; uint8_t v_backend_2409_; lean_object* v_platformIndependent_2410_; uint8_t v_precompileImports_2411_; lean_object* v_dynlibs_2412_; lean_object* v_plugins_2413_; uint8_t v_requiresModuleSystem_2414_; uint8_t v_allowNonModules_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2425_; 
v_buildType_2398_ = lean_ctor_get_uint8(v_cfg_2397_, sizeof(void*)*13);
v_leanOptions_2399_ = lean_ctor_get(v_cfg_2397_, 0);
v_moreLeanArgs_2400_ = lean_ctor_get(v_cfg_2397_, 1);
v_weakLeanArgs_2401_ = lean_ctor_get(v_cfg_2397_, 2);
v_moreLeancArgs_2402_ = lean_ctor_get(v_cfg_2397_, 3);
v_moreServerOptions_2403_ = lean_ctor_get(v_cfg_2397_, 4);
v_weakLeancArgs_2404_ = lean_ctor_get(v_cfg_2397_, 5);
v_moreLinkObjs_2405_ = lean_ctor_get(v_cfg_2397_, 6);
v_moreLinkLibs_2406_ = lean_ctor_get(v_cfg_2397_, 7);
v_moreLinkArgs_2407_ = lean_ctor_get(v_cfg_2397_, 8);
v_weakLinkArgs_2408_ = lean_ctor_get(v_cfg_2397_, 9);
v_backend_2409_ = lean_ctor_get_uint8(v_cfg_2397_, sizeof(void*)*13 + 1);
v_platformIndependent_2410_ = lean_ctor_get(v_cfg_2397_, 10);
v_precompileImports_2411_ = lean_ctor_get_uint8(v_cfg_2397_, sizeof(void*)*13 + 2);
v_dynlibs_2412_ = lean_ctor_get(v_cfg_2397_, 11);
v_plugins_2413_ = lean_ctor_get(v_cfg_2397_, 12);
v_requiresModuleSystem_2414_ = lean_ctor_get_uint8(v_cfg_2397_, sizeof(void*)*13 + 3);
v_allowNonModules_2415_ = lean_ctor_get_uint8(v_cfg_2397_, sizeof(void*)*13 + 4);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_cfg_2397_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2417_ = v_cfg_2397_;
v_isShared_2418_ = v_isSharedCheck_2425_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_plugins_2413_);
lean_inc(v_dynlibs_2412_);
lean_inc(v_platformIndependent_2410_);
lean_inc(v_weakLinkArgs_2408_);
lean_inc(v_moreLinkArgs_2407_);
lean_inc(v_moreLinkLibs_2406_);
lean_inc(v_moreLinkObjs_2405_);
lean_inc(v_weakLeancArgs_2404_);
lean_inc(v_moreServerOptions_2403_);
lean_inc(v_moreLeancArgs_2402_);
lean_inc(v_weakLeanArgs_2401_);
lean_inc(v_moreLeanArgs_2400_);
lean_inc(v_leanOptions_2399_);
lean_dec(v_cfg_2397_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2425_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2422_; 
v___x_2419_ = lean_box(v_allowNonModules_2415_);
v___x_2420_ = lean_apply_1(v_f_2396_, v___x_2419_);
if (v_isShared_2418_ == 0)
{
v___x_2422_ = v___x_2417_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_leanOptions_2399_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_moreLeanArgs_2400_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_weakLeanArgs_2401_);
lean_ctor_set(v_reuseFailAlloc_2424_, 3, v_moreLeancArgs_2402_);
lean_ctor_set(v_reuseFailAlloc_2424_, 4, v_moreServerOptions_2403_);
lean_ctor_set(v_reuseFailAlloc_2424_, 5, v_weakLeancArgs_2404_);
lean_ctor_set(v_reuseFailAlloc_2424_, 6, v_moreLinkObjs_2405_);
lean_ctor_set(v_reuseFailAlloc_2424_, 7, v_moreLinkLibs_2406_);
lean_ctor_set(v_reuseFailAlloc_2424_, 8, v_moreLinkArgs_2407_);
lean_ctor_set(v_reuseFailAlloc_2424_, 9, v_weakLinkArgs_2408_);
lean_ctor_set(v_reuseFailAlloc_2424_, 10, v_platformIndependent_2410_);
lean_ctor_set(v_reuseFailAlloc_2424_, 11, v_dynlibs_2412_);
lean_ctor_set(v_reuseFailAlloc_2424_, 12, v_plugins_2413_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*13, v_buildType_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*13 + 1, v_backend_2409_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*13 + 2, v_precompileImports_2411_);
lean_ctor_set_uint8(v_reuseFailAlloc_2424_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2414_);
v___x_2422_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
uint8_t v___x_2423_; 
v___x_2423_ = lean_unbox(v___x_2420_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*13 + 4, v___x_2423_);
return v___x_2422_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2444_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2445_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2446_ = lean_array_push(v___x_2445_, v___x_2444_);
return v___x_2446_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2454_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2455_ = lean_array_push(v___x_2454_, v___x_2453_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2462_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2463_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2464_ = lean_array_push(v___x_2463_, v___x_2462_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2472_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2473_ = lean_array_push(v___x_2472_, v___x_2471_);
return v___x_2473_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2481_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2482_ = lean_array_push(v___x_2481_, v___x_2480_);
return v___x_2482_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2490_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2491_ = lean_array_push(v___x_2490_, v___x_2489_);
return v___x_2491_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2498_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2499_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2500_ = lean_array_push(v___x_2499_, v___x_2498_);
return v___x_2500_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2507_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2508_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2509_ = lean_array_push(v___x_2508_, v___x_2507_);
return v___x_2509_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2516_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2517_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2518_ = lean_array_push(v___x_2517_, v___x_2516_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2526_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2527_ = lean_array_push(v___x_2526_, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2534_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2535_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2536_ = lean_array_push(v___x_2535_, v___x_2534_);
return v___x_2536_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2544_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2545_ = lean_array_push(v___x_2544_, v___x_2543_);
return v___x_2545_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2552_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2553_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2554_ = lean_array_push(v___x_2553_, v___x_2552_);
return v___x_2554_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2561_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2562_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2563_ = lean_array_push(v___x_2562_, v___x_2561_);
return v___x_2563_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2570_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2571_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2572_ = lean_array_push(v___x_2571_, v___x_2570_);
return v___x_2572_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__47));
v___x_2580_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
v___x_2581_ = lean_array_push(v___x_2580_, v___x_2579_);
return v___x_2581_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__51(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__50));
v___x_2589_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__48, &l_Lake_LeanConfig___fields___closed__48_once, _init_l_Lake_LeanConfig___fields___closed__48);
v___x_2590_ = lean_array_push(v___x_2589_, v___x_2588_);
return v___x_2590_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__54(void){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__53));
v___x_2598_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__51, &l_Lake_LeanConfig___fields___closed__51_once, _init_l_Lake_LeanConfig___fields___closed__51);
v___x_2599_ = lean_array_push(v___x_2598_, v___x_2597_);
return v___x_2599_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__54, &l_Lake_LeanConfig___fields___closed__54_once, _init_l_Lake_LeanConfig___fields___closed__54);
return v___x_2600_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lake_LeanConfig___fields;
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2602_, lean_object* v_x2_2603_){
_start:
{
lean_object* v_name_2604_; lean_object* v___x_2605_; 
v_name_2604_ = lean_ctor_get(v_x2_2603_, 0);
lean_inc(v_name_2604_);
v___x_2605_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2604_, v_x2_2603_, v_x1_2602_);
return v___x_2605_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = l_Lake_LeanConfig___fields;
v___x_2607_ = lean_array_get_size(v___x_2606_);
return v___x_2607_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2627_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_nat_dec_lt(v___x_2628_, v___x_2627_);
return v___x_2629_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2630_ = lean_unsigned_to_nat(0u);
v___x_2631_ = lean_box(1);
v___x_2632_ = l_Lake_LeanConfig___fields;
v___x_2633_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v___x_2631_);
lean_ctor_set(v___x_2633_, 2, v___x_2630_);
return v___x_2633_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2635_; uint8_t v___x_2636_; 
v___x_2635_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2636_ = lean_nat_dec_le(v___x_2635_, v___x_2635_);
return v___x_2636_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2637_; size_t v___x_2638_; 
v___x_2637_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2638_ = lean_usize_of_nat(v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2639_; size_t v___x_2640_; size_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___f_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2639_ = lean_box(1);
v___x_2640_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = l_Lake_LeanConfig___fields;
v___f_2643_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2644_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2644_, v___f_2643_, v___x_2642_, v___x_2641_, v___x_2640_, v___x_2639_);
return v___x_2645_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2646_ = lean_unsigned_to_nat(0u);
v___x_2647_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2648_ = l_Lake_LeanConfig___fields;
v___x_2649_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2649_, 0, v___x_2648_);
lean_ctor_set(v___x_2649_, 1, v___x_2647_);
lean_ctor_set(v___x_2649_, 2, v___x_2646_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2650_ == 0)
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2651_;
}
else
{
uint8_t v___x_2652_; 
v___x_2652_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2652_ == 0)
{
if (v___x_2650_ == 0)
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2653_;
}
else
{
lean_object* v___x_2654_; 
v___x_2654_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2654_;
}
}
else
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2655_;
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

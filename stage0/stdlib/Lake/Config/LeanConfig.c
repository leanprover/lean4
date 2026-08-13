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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lake_Target_repr___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_instReprLeanOption_repr___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___boxed(lean_object*);
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
static const lean_array_object l_Lake_BuildType_leanArgs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_BuildType_leanArgs___closed__0 = (const lean_object*)&l_Lake_BuildType_leanArgs___closed__0_value;
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
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "dynlibs"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__38 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__38_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__38_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__39 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__39_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "plugins"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__40 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__40_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__40_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__41 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__41_value;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "requiresModuleSystem"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__43 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__43_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__44;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "allowNonModules"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__45 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__45_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__45_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__46 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__46_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__47;
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__48 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__48_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__49;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__50;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__51 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__51_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__48_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__52 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__52_value;
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
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0_value;
static const lean_closure_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1_value;
static const lean_closure_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2_value;
static const lean_closure_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value;
static const lean_ctor_object l_Lake_LeanConfig_requiresModuleSystem___proj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value)}};
static const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___closed__4 = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__4_value;
LEAN_EXPORT const lean_object* l_Lake_LeanConfig_requiresModuleSystem_instConfigField = (const lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__4_value;
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
static const lean_ctor_object l_Lake_LeanConfig_allowNonModules___proj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__0_value),((lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__1_value),((lean_object*)&l_Lake_LeanConfig_allowNonModules___proj___closed__2_value),((lean_object*)&l_Lake_LeanConfig_requiresModuleSystem___proj___closed__3_value)}};
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
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__38_value),LEAN_SCALAR_PTR_LITERAL(213, 126, 44, 113, 100, 173, 176, 199)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__40 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__40_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__40_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__40_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__41 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__41_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__42_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__42;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__40_value),LEAN_SCALAR_PTR_LITERAL(43, 100, 103, 72, 156, 88, 10, 236)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__43 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__43_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__43_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__43_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__44 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__44_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__45;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value),LEAN_SCALAR_PTR_LITERAL(9, 5, 144, 35, 76, 175, 146, 150)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__46 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__46_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__46_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__46_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__47 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__47_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__48;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__45_value),LEAN_SCALAR_PTR_LITERAL(196, 92, 18, 175, 109, 198, 159, 30)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__49 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__49_value;
static const lean_ctor_object l_Lake_LeanConfig___fields___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_LeanConfig___fields___closed__49_value),((lean_object*)&l_Lake_LeanConfig___fields___closed__49_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_LeanConfig___fields___closed__50 = (const lean_object*)&l_Lake_LeanConfig___fields___closed__50_value;
static lean_once_cell_t l_Lake_LeanConfig___fields___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_LeanConfig___fields___closed__51;
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
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
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
LEAN_EXPORT lean_object* l_Lake_Backend_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lake_Backend_ctorIdx(v_x_boxed_6_);
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
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lake_Backend_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg(lean_object* v_c_23_){
_start:
{
lean_inc(v_c_23_);
return v_c_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg___boxed(lean_object* v_c_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lake_Backend_c_elim___redArg(v_c_24_);
lean_dec(v_c_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_c_29_){
_start:
{
lean_inc(v_c_29_);
return v_c_29_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_c_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lake_Backend_c_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_c_33_);
lean_dec(v_c_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg(lean_object* v_llvm_36_){
_start:
{
lean_inc(v_llvm_36_);
return v_llvm_36_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg___boxed(lean_object* v_llvm_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_Backend_llvm_elim___redArg(v_llvm_37_);
lean_dec(v_llvm_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_llvm_42_){
_start:
{
lean_inc(v_llvm_42_);
return v_llvm_42_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_llvm_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lake_Backend_llvm_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_llvm_46_);
lean_dec(v_llvm_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg(lean_object* v_default_49_){
_start:
{
lean_inc(v_default_49_);
return v_default_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg___boxed(lean_object* v_default_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lake_Backend_default_elim___redArg(v_default_50_);
lean_dec(v_default_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_default_55_){
_start:
{
lean_inc(v_default_55_);
return v_default_55_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_default_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lake_Backend_default_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_default_59_);
lean_dec(v_default_59_);
return v_res_61_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__6(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr(uint8_t v_x_75_, lean_object* v_prec_76_){
_start:
{
lean_object* v___y_78_; lean_object* v___y_85_; lean_object* v___y_92_; 
switch(v_x_75_)
{
case 0:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(1024u);
v___x_99_ = lean_nat_dec_le(v___x_98_, v_prec_76_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_78_ = v___x_100_;
goto v___jp_77_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_78_ = v___x_101_;
goto v___jp_77_;
}
}
case 1:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1024u);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_prec_76_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_85_ = v___x_104_;
goto v___jp_84_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_85_ = v___x_105_;
goto v___jp_84_;
}
}
default: 
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = lean_unsigned_to_nat(1024u);
v___x_107_ = lean_nat_dec_le(v___x_106_, v_prec_76_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_92_ = v___x_108_;
goto v___jp_91_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_92_ = v___x_109_;
goto v___jp_91_;
}
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__1));
lean_inc(v___y_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___y_78_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = 0;
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_81_);
v___x_83_ = l_Repr_addAppParen(v___x_82_, v_prec_76_);
return v___x_83_;
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__3));
lean_inc(v___y_85_);
v___x_87_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_87_, 0, v___y_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = 0;
v___x_89_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set_uint8(v___x_89_, sizeof(void*)*1, v___x_88_);
v___x_90_ = l_Repr_addAppParen(v___x_89_, v_prec_76_);
return v___x_90_;
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__5));
lean_inc(v___y_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___y_92_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = 0;
v___x_96_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_96_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*1, v___x_95_);
v___x_97_ = l_Repr_addAppParen(v___x_96_, v_prec_76_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
uint8_t v_x_177__boxed_112_; lean_object* v_res_113_; 
v_x_177__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Lake_instReprBackend_repr(v_x_177__boxed_112_, v_prec_111_);
lean_dec(v_prec_111_);
return v_res_113_;
}
}
LEAN_EXPORT uint8_t l_Lake_Backend_ofNat(lean_object* v_n_116_){
_start:
{
lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_nat_dec_le(v_n_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_dec_le(v_n_116_, v___x_119_);
if (v___x_120_ == 0)
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
else
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofNat___boxed(lean_object* v_n_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = l_Lake_Backend_ofNat(v_n_124_);
lean_dec(v_n_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBackend(uint8_t v_x_127_, uint8_t v_y_128_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_129_ = l_Lake_Backend_ctorIdx(v_x_127_);
v___x_130_ = l_Lake_Backend_ctorIdx(v_y_128_);
v___x_131_ = lean_nat_dec_eq(v___x_129_, v___x_130_);
lean_dec(v___x_130_);
lean_dec(v___x_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBackend___boxed(lean_object* v_x_132_, lean_object* v_y_133_){
_start:
{
uint8_t v_x_13__boxed_134_; uint8_t v_y_14__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_x_13__boxed_134_ = lean_unbox(v_x_132_);
v_y_14__boxed_135_ = lean_unbox(v_y_133_);
v_res_136_ = l_Lake_instDecidableEqBackend(v_x_13__boxed_134_, v_y_14__boxed_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
static uint8_t _init_l_Lake_Backend_instInhabited(void){
_start:
{
uint8_t v___x_138_; 
v___x_138_ = 2;
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f(lean_object* v_s_151_){
_start:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
v___x_153_ = lean_string_dec_eq(v_s_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
v___x_155_ = lean_string_dec_eq(v_s_151_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
v___x_157_ = lean_string_dec_eq(v_s_151_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_box(0);
return v___x_158_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__3));
return v___x_159_;
}
}
else
{
lean_object* v___x_160_; 
v___x_160_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__4));
return v___x_160_;
}
}
else
{
lean_object* v___x_161_; 
v___x_161_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__5));
return v___x_161_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f___boxed(lean_object* v_s_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lake_Backend_ofString_x3f(v_s_162_);
lean_dec_ref(v_s_162_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_toString(uint8_t v_bt_164_){
_start:
{
switch(v_bt_164_)
{
case 0:
{
lean_object* v___x_165_; 
v___x_165_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
return v___x_165_;
}
case 1:
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
return v___x_166_;
}
default: 
{
lean_object* v___x_167_; 
v___x_167_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_toString___boxed(lean_object* v_bt_168_){
_start:
{
uint8_t v_bt_boxed_169_; lean_object* v_res_170_; 
v_bt_boxed_169_ = lean_unbox(v_bt_168_);
v_res_170_ = l_Lake_Backend_toString(v_bt_boxed_169_);
return v_res_170_;
}
}
LEAN_EXPORT uint8_t l_Lake_Backend_orPreferLeft(uint8_t v_x_173_, uint8_t v_x_174_){
_start:
{
if (v_x_173_ == 2)
{
return v_x_174_;
}
else
{
return v_x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_orPreferLeft___boxed(lean_object* v_x_175_, lean_object* v_x_176_){
_start:
{
uint8_t v_x_16__boxed_177_; uint8_t v_x_17__boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_x_16__boxed_177_ = lean_unbox(v_x_175_);
v_x_17__boxed_178_ = lean_unbox(v_x_176_);
v_res_179_ = l_Lake_Backend_orPreferLeft(v_x_16__boxed_177_, v_x_17__boxed_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx(uint8_t v_x_181_){
_start:
{
switch(v_x_181_)
{
case 0:
{
lean_object* v___x_182_; 
v___x_182_ = lean_unsigned_to_nat(0u);
return v___x_182_;
}
case 1:
{
lean_object* v___x_183_; 
v___x_183_ = lean_unsigned_to_nat(1u);
return v___x_183_;
}
case 2:
{
lean_object* v___x_184_; 
v___x_184_ = lean_unsigned_to_nat(2u);
return v___x_184_;
}
default: 
{
lean_object* v___x_185_; 
v___x_185_ = lean_unsigned_to_nat(3u);
return v___x_185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___boxed(lean_object* v_x_186_){
_start:
{
uint8_t v_x_boxed_187_; lean_object* v_res_188_; 
v_x_boxed_187_ = lean_unbox(v_x_186_);
v_res_188_ = l_Lake_BuildType_ctorIdx(v_x_boxed_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg(lean_object* v_k_189_){
_start:
{
lean_inc(v_k_189_);
return v_k_189_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___redArg___boxed(lean_object* v_k_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lake_BuildType_ctorElim___redArg(v_k_190_);
lean_dec(v_k_190_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim(lean_object* v_motive_192_, lean_object* v_ctorIdx_193_, uint8_t v_t_194_, lean_object* v_h_195_, lean_object* v_k_196_){
_start:
{
lean_inc(v_k_196_);
return v_k_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___boxed(lean_object* v_motive_197_, lean_object* v_ctorIdx_198_, lean_object* v_t_199_, lean_object* v_h_200_, lean_object* v_k_201_){
_start:
{
uint8_t v_t_boxed_202_; lean_object* v_res_203_; 
v_t_boxed_202_ = lean_unbox(v_t_199_);
v_res_203_ = l_Lake_BuildType_ctorElim(v_motive_197_, v_ctorIdx_198_, v_t_boxed_202_, v_h_200_, v_k_201_);
lean_dec(v_k_201_);
lean_dec(v_ctorIdx_198_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg(lean_object* v_debug_204_){
_start:
{
lean_inc(v_debug_204_);
return v_debug_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg___boxed(lean_object* v_debug_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lake_BuildType_debug_elim___redArg(v_debug_205_);
lean_dec(v_debug_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim(lean_object* v_motive_207_, uint8_t v_t_208_, lean_object* v_h_209_, lean_object* v_debug_210_){
_start:
{
lean_inc(v_debug_210_);
return v_debug_210_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___boxed(lean_object* v_motive_211_, lean_object* v_t_212_, lean_object* v_h_213_, lean_object* v_debug_214_){
_start:
{
uint8_t v_t_boxed_215_; lean_object* v_res_216_; 
v_t_boxed_215_ = lean_unbox(v_t_212_);
v_res_216_ = l_Lake_BuildType_debug_elim(v_motive_211_, v_t_boxed_215_, v_h_213_, v_debug_214_);
lean_dec(v_debug_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg(lean_object* v_relWithDebInfo_217_){
_start:
{
lean_inc(v_relWithDebInfo_217_);
return v_relWithDebInfo_217_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg___boxed(lean_object* v_relWithDebInfo_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lake_BuildType_relWithDebInfo_elim___redArg(v_relWithDebInfo_218_);
lean_dec(v_relWithDebInfo_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim(lean_object* v_motive_220_, uint8_t v_t_221_, lean_object* v_h_222_, lean_object* v_relWithDebInfo_223_){
_start:
{
lean_inc(v_relWithDebInfo_223_);
return v_relWithDebInfo_223_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___boxed(lean_object* v_motive_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_relWithDebInfo_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lake_BuildType_relWithDebInfo_elim(v_motive_224_, v_t_boxed_228_, v_h_226_, v_relWithDebInfo_227_);
lean_dec(v_relWithDebInfo_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg(lean_object* v_minSizeRel_230_){
_start:
{
lean_inc(v_minSizeRel_230_);
return v_minSizeRel_230_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg___boxed(lean_object* v_minSizeRel_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lake_BuildType_minSizeRel_elim___redArg(v_minSizeRel_231_);
lean_dec(v_minSizeRel_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_minSizeRel_236_){
_start:
{
lean_inc(v_minSizeRel_236_);
return v_minSizeRel_236_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_minSizeRel_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lake_BuildType_minSizeRel_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_minSizeRel_240_);
lean_dec(v_minSizeRel_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg(lean_object* v_release_243_){
_start:
{
lean_inc(v_release_243_);
return v_release_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg___boxed(lean_object* v_release_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lake_BuildType_release_elim___redArg(v_release_244_);
lean_dec(v_release_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_release_249_){
_start:
{
lean_inc(v_release_249_);
return v_release_249_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_release_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lake_BuildType_release_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_release_253_);
lean_dec(v_release_253_);
return v_res_255_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType_default(void){
_start:
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType(void){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = 0;
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr(uint8_t v_x_270_, lean_object* v_prec_271_){
_start:
{
lean_object* v___y_273_; lean_object* v___y_280_; lean_object* v___y_287_; lean_object* v___y_294_; 
switch(v_x_270_)
{
case 0:
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1024u);
v___x_301_ = lean_nat_dec_le(v___x_300_, v_prec_271_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_273_ = v___x_302_;
goto v___jp_272_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_273_ = v___x_303_;
goto v___jp_272_;
}
}
case 1:
{
lean_object* v___x_304_; uint8_t v___x_305_; 
v___x_304_ = lean_unsigned_to_nat(1024u);
v___x_305_ = lean_nat_dec_le(v___x_304_, v_prec_271_);
if (v___x_305_ == 0)
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_280_ = v___x_306_;
goto v___jp_279_;
}
else
{
lean_object* v___x_307_; 
v___x_307_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_280_ = v___x_307_;
goto v___jp_279_;
}
}
case 2:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_unsigned_to_nat(1024u);
v___x_309_ = lean_nat_dec_le(v___x_308_, v_prec_271_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_287_ = v___x_310_;
goto v___jp_286_;
}
else
{
lean_object* v___x_311_; 
v___x_311_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_287_ = v___x_311_;
goto v___jp_286_;
}
}
default: 
{
lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1024u);
v___x_313_ = lean_nat_dec_le(v___x_312_, v_prec_271_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; 
v___x_314_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_294_ = v___x_314_;
goto v___jp_293_;
}
else
{
lean_object* v___x_315_; 
v___x_315_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_294_ = v___x_315_;
goto v___jp_293_;
}
}
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_274_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__1));
lean_inc(v___y_273_);
v___x_275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_275_, 0, v___y_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = 0;
v___x_277_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_277_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_277_, sizeof(void*)*1, v___x_276_);
v___x_278_ = l_Repr_addAppParen(v___x_277_, v_prec_271_);
return v___x_278_;
}
v___jp_279_:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_281_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__3));
lean_inc(v___y_280_);
v___x_282_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_282_, 0, v___y_280_);
lean_ctor_set(v___x_282_, 1, v___x_281_);
v___x_283_ = 0;
v___x_284_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_284_, 0, v___x_282_);
lean_ctor_set_uint8(v___x_284_, sizeof(void*)*1, v___x_283_);
v___x_285_ = l_Repr_addAppParen(v___x_284_, v_prec_271_);
return v___x_285_;
}
v___jp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_288_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__5));
lean_inc(v___y_287_);
v___x_289_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_289_, 0, v___y_287_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = 0;
v___x_291_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v___x_290_);
v___x_292_ = l_Repr_addAppParen(v___x_291_, v_prec_271_);
return v___x_292_;
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_295_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__7));
lean_inc(v___y_294_);
v___x_296_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_296_, 0, v___y_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = 0;
v___x_298_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_298_, 0, v___x_296_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*1, v___x_297_);
v___x_299_ = l_Repr_addAppParen(v___x_298_, v_prec_271_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr___boxed(lean_object* v_x_316_, lean_object* v_prec_317_){
_start:
{
uint8_t v_x_229__boxed_318_; lean_object* v_res_319_; 
v_x_229__boxed_318_ = lean_unbox(v_x_316_);
v_res_319_ = l_Lake_instReprBuildType_repr(v_x_229__boxed_318_, v_prec_317_);
lean_dec(v_prec_317_);
return v_res_319_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_ofNat(lean_object* v_n_322_){
_start:
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_unsigned_to_nat(1u);
v___x_324_ = lean_nat_dec_le(v_n_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(2u);
v___x_326_ = lean_nat_dec_le(v_n_322_, v___x_325_);
if (v___x_326_ == 0)
{
uint8_t v___x_327_; 
v___x_327_ = 3;
return v___x_327_;
}
else
{
uint8_t v___x_328_; 
v___x_328_ = 2;
return v___x_328_;
}
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(0u);
v___x_330_ = lean_nat_dec_le(v_n_322_, v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; 
v___x_331_ = 1;
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = 0;
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofNat___boxed(lean_object* v_n_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lake_BuildType_ofNat(v_n_333_);
lean_dec(v_n_333_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildType(uint8_t v_x_336_, uint8_t v_y_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_338_ = l_Lake_BuildType_ctorIdx(v_x_336_);
v___x_339_ = l_Lake_BuildType_ctorIdx(v_y_337_);
v___x_340_ = lean_nat_dec_eq(v___x_338_, v___x_339_);
lean_dec(v___x_339_);
lean_dec(v___x_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildType___boxed(lean_object* v_x_341_, lean_object* v_y_342_){
_start:
{
uint8_t v_x_13__boxed_343_; uint8_t v_y_14__boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_x_13__boxed_343_ = lean_unbox(v_x_341_);
v_y_14__boxed_344_ = lean_unbox(v_y_342_);
v_res_345_ = l_Lake_instDecidableEqBuildType(v_x_13__boxed_343_, v_y_14__boxed_344_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdBuildType_ord(uint8_t v_x_347_, uint8_t v_y_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = l_Lake_BuildType_ctorIdx(v_x_347_);
v___x_350_ = l_Lake_BuildType_ctorIdx(v_y_348_);
v___x_351_ = lean_nat_dec_lt(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_eq(v___x_349_, v___x_350_);
lean_dec(v___x_350_);
lean_dec(v___x_349_);
if (v___x_352_ == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 2;
return v___x_353_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = 1;
return v___x_354_;
}
}
else
{
uint8_t v___x_355_; 
lean_dec(v___x_350_);
lean_dec(v___x_349_);
v___x_355_ = 0;
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdBuildType_ord___boxed(lean_object* v_x_356_, lean_object* v_y_357_){
_start:
{
uint8_t v_x_30__boxed_358_; uint8_t v_y_31__boxed_359_; uint8_t v_res_360_; lean_object* v_r_361_; 
v_x_30__boxed_358_ = lean_unbox(v_x_356_);
v_y_31__boxed_359_ = lean_unbox(v_y_357_);
v_res_360_ = l_Lake_instOrdBuildType_ord(v_x_30__boxed_358_, v_y_31__boxed_359_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
static lean_object* _init_l_Lake_BuildType_instLT(void){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
}
static lean_object* _init_l_Lake_BuildType_instLE(void){
_start:
{
lean_object* v___x_365_; 
v___x_365_ = lean_box(0);
return v___x_365_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_instMin___lam__0(uint8_t v_x_366_, uint8_t v_y_367_){
_start:
{
uint8_t v___x_368_; 
v___x_368_ = l_Lake_instOrdBuildType_ord(v_x_366_, v_y_367_);
if (v___x_368_ == 2)
{
return v_y_367_;
}
else
{
return v_x_366_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMin___lam__0___boxed(lean_object* v_x_369_, lean_object* v_y_370_){
_start:
{
uint8_t v_x_boxed_371_; uint8_t v_y_boxed_372_; uint8_t v_res_373_; lean_object* v_r_374_; 
v_x_boxed_371_ = lean_unbox(v_x_369_);
v_y_boxed_372_ = lean_unbox(v_y_370_);
v_res_373_ = l_Lake_BuildType_instMin___lam__0(v_x_boxed_371_, v_y_boxed_372_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_instMax___lam__0(uint8_t v_x_377_, uint8_t v_y_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = l_Lake_instOrdBuildType_ord(v_x_377_, v_y_378_);
if (v___x_379_ == 2)
{
return v_x_377_;
}
else
{
return v_y_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMax___lam__0___boxed(lean_object* v_x_380_, lean_object* v_y_381_){
_start:
{
uint8_t v_x_boxed_382_; uint8_t v_y_boxed_383_; uint8_t v_res_384_; lean_object* v_r_385_; 
v_x_boxed_382_ = lean_unbox(v_x_380_);
v_y_boxed_383_ = lean_unbox(v_y_381_);
v_res_384_ = l_Lake_BuildType_instMax___lam__0(v_x_boxed_382_, v_y_boxed_383_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs(uint8_t v_x_419_){
_start:
{
switch(v_x_419_)
{
case 0:
{
lean_object* v___x_420_; 
v___x_420_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__2));
return v___x_420_;
}
case 1:
{
lean_object* v___x_421_; 
v___x_421_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__5));
return v___x_421_;
}
case 2:
{
lean_object* v___x_422_; 
v___x_422_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__7));
return v___x_422_;
}
default: 
{
lean_object* v___x_423_; 
v___x_423_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__8));
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs___boxed(lean_object* v_x_424_){
_start:
{
uint8_t v_x_163__boxed_425_; lean_object* v_res_426_; 
v_x_163__boxed_425_ = lean_unbox(v_x_424_);
v_res_426_ = l_Lake_BuildType_leancArgs(v_x_163__boxed_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofString_x3f(lean_object* v_s_443_){
_start:
{
lean_object* v___y_445_; lean_object* v___x_459_; uint32_t v___x_460_; uint32_t v___x_461_; uint8_t v___x_462_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_string_utf8_get(v_s_443_, v___x_459_);
v___x_461_ = 65;
v___x_462_ = lean_uint32_dec_le(v___x_461_, v___x_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
v___x_463_ = lean_string_utf8_set(v_s_443_, v___x_459_, v___x_460_);
v___y_445_ = v___x_463_;
goto v___jp_444_;
}
else
{
uint32_t v___x_464_; uint8_t v___x_465_; 
v___x_464_ = 90;
v___x_465_ = lean_uint32_dec_le(v___x_460_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_string_utf8_set(v_s_443_, v___x_459_, v___x_460_);
v___y_445_ = v___x_466_;
goto v___jp_444_;
}
else
{
uint32_t v___x_467_; uint32_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = 32;
v___x_468_ = lean_uint32_add(v___x_460_, v___x_467_);
v___x_469_ = lean_string_utf8_set(v_s_443_, v___x_459_, v___x_468_);
v___y_445_ = v___x_469_;
goto v___jp_444_;
}
}
v___jp_444_:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
v___x_447_ = lean_string_dec_eq(v___y_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
v___x_449_ = lean_string_dec_eq(v___y_445_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
v___x_451_ = lean_string_dec_eq(v___y_445_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
v___x_453_ = lean_string_dec_eq(v___y_445_, v___x_452_);
lean_dec_ref(v___y_445_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; 
v___x_454_ = lean_box(0);
return v___x_454_;
}
else
{
lean_object* v___x_455_; 
v___x_455_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__4));
return v___x_455_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec_ref(v___y_445_);
v___x_456_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__5));
return v___x_456_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec_ref(v___y_445_);
v___x_457_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__6));
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v___y_445_);
v___x_458_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__7));
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString(uint8_t v_bt_470_){
_start:
{
switch(v_bt_470_)
{
case 0:
{
lean_object* v___x_471_; 
v___x_471_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
return v___x_471_;
}
case 1:
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
return v___x_472_;
}
case 2:
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
return v___x_473_;
}
default: 
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString___boxed(lean_object* v_bt_475_){
_start:
{
uint8_t v_bt_boxed_476_; lean_object* v_res_477_; 
v_bt_boxed_476_ = lean_unbox(v_bt_475_);
v_res_477_ = l_Lake_BuildType_toString(v_bt_boxed_476_);
return v_res_477_;
}
}
static lean_object* _init_l_Lake_BuildType_leanOptions___closed__3(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_485_ = lean_box(1);
v___x_486_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__2));
v___x_487_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__1));
v___x_488_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_487_, v___x_486_, v___x_485_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions(uint8_t v_x_489_){
_start:
{
if (v_x_489_ == 0)
{
lean_object* v___x_490_; 
v___x_490_ = lean_obj_once(&l_Lake_BuildType_leanOptions___closed__3, &l_Lake_BuildType_leanOptions___closed__3_once, _init_l_Lake_BuildType_leanOptions___closed__3);
return v___x_490_;
}
else
{
lean_object* v___x_491_; 
v___x_491_ = lean_box(1);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions___boxed(lean_object* v_x_492_){
_start:
{
uint8_t v_x_70__boxed_493_; lean_object* v_res_494_; 
v_x_70__boxed_493_ = lean_unbox(v_x_492_);
v_res_494_ = l_Lake_BuildType_leanOptions(v_x_70__boxed_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs(uint8_t v_t_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___boxed(lean_object* v_t_499_){
_start:
{
uint8_t v_t_boxed_500_; lean_object* v_res_501_; 
v_t_boxed_500_ = lean_unbox(v_t_499_);
v_res_501_ = l_Lake_BuildType_leanArgs(v_t_boxed_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object* v_x_518_, lean_object* v_x_519_){
_start:
{
if (lean_obj_tag(v_x_518_) == 0)
{
lean_object* v___x_520_; 
v___x_520_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1));
return v___x_520_;
}
else
{
lean_object* v_val_521_; lean_object* v___x_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; 
v_val_521_ = lean_ctor_get(v_x_518_, 0);
v___x_522_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3));
v___x_523_ = lean_unbox(v_val_521_);
v___x_524_ = l_Bool_repr___redArg(v___x_523_);
v___x_525_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_522_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = l_Repr_addAppParen(v___x_525_, v_x_519_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_527_, v_x_528_);
lean_dec(v_x_528_);
lean_dec(v_x_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object* v_a_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_nat_to_int(v_a_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object* v___y_532_){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = l_String_quote(v___y_532_);
v___x_534_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
if (lean_obj_tag(v_x_537_) == 0)
{
lean_dec(v_x_535_);
return v_x_536_;
}
else
{
lean_object* v_head_538_; lean_object* v_tail_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_550_; 
v_head_538_ = lean_ctor_get(v_x_537_, 0);
v_tail_539_ = lean_ctor_get(v_x_537_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_x_537_);
if (v_isSharedCheck_550_ == 0)
{
v___x_541_ = v_x_537_;
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_tail_539_);
lean_inc(v_head_538_);
lean_dec(v_x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
lean_inc(v_x_535_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 5);
lean_ctor_set(v___x_541_, 1, v_x_535_);
lean_ctor_set(v___x_541_, 0, v_x_536_);
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_x_536_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_x_535_);
v___x_544_ = v_reuseFailAlloc_549_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = l_String_quote(v_head_538_);
v___x_546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_544_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v_x_536_ = v___x_547_;
v_x_537_ = v_tail_539_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
lean_dec(v_x_551_);
return v_x_552_;
}
else
{
lean_object* v_head_554_; lean_object* v_tail_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_566_; 
v_head_554_ = lean_ctor_get(v_x_553_, 0);
v_tail_555_ = lean_ctor_get(v_x_553_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_x_553_);
if (v_isSharedCheck_566_ == 0)
{
v___x_557_ = v_x_553_;
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_tail_555_);
lean_inc(v_head_554_);
lean_dec(v_x_553_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_566_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
lean_inc(v_x_551_);
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 5);
lean_ctor_set(v___x_557_, 1, v_x_551_);
lean_ctor_set(v___x_557_, 0, v_x_552_);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_x_552_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_x_551_);
v___x_560_ = v_reuseFailAlloc_565_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = l_String_quote(v_head_554_);
v___x_562_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___x_563_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_560_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
v___x_564_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_551_, v___x_563_, v_tail_555_);
return v___x_564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object* v_x_567_, lean_object* v_x_568_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v___x_569_; 
lean_dec(v_x_568_);
v___x_569_ = lean_box(0);
return v___x_569_;
}
else
{
lean_object* v_tail_570_; 
v_tail_570_ = lean_ctor_get(v_x_567_, 1);
if (lean_obj_tag(v_tail_570_) == 0)
{
lean_object* v_head_571_; lean_object* v___x_572_; 
lean_dec(v_x_568_);
v_head_571_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_head_571_);
lean_dec_ref_known(v_x_567_, 2);
v___x_572_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_571_);
return v___x_572_;
}
else
{
lean_object* v_head_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
lean_inc(v_tail_570_);
v_head_573_ = lean_ctor_get(v_x_567_, 0);
lean_inc(v_head_573_);
lean_dec_ref_known(v_x_567_, 2);
v___x_574_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_573_);
v___x_575_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_568_, v___x_574_, v_tail_570_);
return v___x_575_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0));
v___x_585_ = lean_string_length(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5);
v___x_587_ = lean_nat_to_int(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object* v_xs_595_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_array_get_size(v_xs_595_);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_nat_dec_eq(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_599_ = lean_array_to_list(v_xs_595_);
v___x_600_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_601_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_599_, v___x_600_);
v___x_602_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_603_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_604_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
lean_ctor_set(v___x_604_, 1, v___x_601_);
v___x_605_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_606_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_602_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Std_Format_fill(v___x_607_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
lean_dec_ref(v_xs_595_);
v___x_609_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object* v___y_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l_Lake_Target_repr___redArg(v___y_610_, v___x_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_){
_start:
{
if (lean_obj_tag(v_x_615_) == 0)
{
lean_dec(v_x_613_);
return v_x_614_;
}
else
{
lean_object* v_head_616_; lean_object* v_tail_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_628_; 
v_head_616_ = lean_ctor_get(v_x_615_, 0);
v_tail_617_ = lean_ctor_get(v_x_615_, 1);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_615_);
if (v_isSharedCheck_628_ == 0)
{
v___x_619_ = v_x_615_;
v_isShared_620_ = v_isSharedCheck_628_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_tail_617_);
lean_inc(v_head_616_);
lean_dec(v_x_615_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_628_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
lean_inc(v_x_613_);
if (v_isShared_620_ == 0)
{
lean_ctor_set_tag(v___x_619_, 5);
lean_ctor_set(v___x_619_, 1, v_x_613_);
lean_ctor_set(v___x_619_, 0, v_x_614_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_x_614_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_x_613_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_Lake_Target_repr___redArg(v_head_616_, v___x_623_);
v___x_625_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_622_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v_x_614_ = v___x_625_;
v_x_615_ = v_tail_617_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_dec(v_x_629_);
return v_x_630_;
}
else
{
lean_object* v_head_632_; lean_object* v_tail_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_644_; 
v_head_632_ = lean_ctor_get(v_x_631_, 0);
v_tail_633_ = lean_ctor_get(v_x_631_, 1);
v_isSharedCheck_644_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_644_ == 0)
{
v___x_635_ = v_x_631_;
v_isShared_636_ = v_isSharedCheck_644_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_tail_633_);
lean_inc(v_head_632_);
lean_dec(v_x_631_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_644_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
lean_inc(v_x_629_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 5);
lean_ctor_set(v___x_635_, 1, v_x_629_);
lean_ctor_set(v___x_635_, 0, v_x_630_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_x_630_);
lean_ctor_set(v_reuseFailAlloc_643_, 1, v_x_629_);
v___x_638_ = v_reuseFailAlloc_643_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = l_Lake_Target_repr___redArg(v_head_632_, v___x_639_);
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_638_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_629_, v___x_641_, v_tail_633_);
return v___x_642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object* v_x_645_, lean_object* v_x_646_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
lean_object* v___x_647_; 
lean_dec(v_x_646_);
v___x_647_ = lean_box(0);
return v___x_647_;
}
else
{
lean_object* v_tail_648_; 
v_tail_648_ = lean_ctor_get(v_x_645_, 1);
if (lean_obj_tag(v_tail_648_) == 0)
{
lean_object* v_head_649_; lean_object* v___x_650_; 
lean_dec(v_x_646_);
v_head_649_ = lean_ctor_get(v_x_645_, 0);
lean_inc(v_head_649_);
lean_dec_ref_known(v_x_645_, 2);
v___x_650_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_649_);
return v___x_650_;
}
else
{
lean_object* v_head_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_inc(v_tail_648_);
v_head_651_ = lean_ctor_get(v_x_645_, 0);
lean_inc(v_head_651_);
lean_dec_ref_known(v_x_645_, 2);
v___x_652_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_651_);
v___x_653_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_646_, v___x_652_, v_tail_648_);
return v___x_653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object* v_xs_654_){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_array_get_size(v_xs_654_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_658_ = lean_array_to_list(v_xs_654_);
v___x_659_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_660_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_658_, v___x_659_);
v___x_661_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_662_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___x_660_);
v___x_664_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_665_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_661_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Std_Format_fill(v___x_666_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
lean_dec_ref(v_xs_654_);
v___x_668_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
if (lean_obj_tag(v_x_671_) == 0)
{
lean_dec(v_x_669_);
return v_x_670_;
}
else
{
lean_object* v_head_672_; lean_object* v_tail_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_683_; 
v_head_672_ = lean_ctor_get(v_x_671_, 0);
v_tail_673_ = lean_ctor_get(v_x_671_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_671_);
if (v_isSharedCheck_683_ == 0)
{
v___x_675_ = v_x_671_;
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_tail_673_);
lean_inc(v_head_672_);
lean_dec(v_x_671_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_683_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
lean_inc(v_x_669_);
if (v_isShared_676_ == 0)
{
lean_ctor_set_tag(v___x_675_, 5);
lean_ctor_set(v___x_675_, 1, v_x_669_);
lean_ctor_set(v___x_675_, 0, v_x_670_);
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_x_670_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v_x_669_);
v___x_678_ = v_reuseFailAlloc_682_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = l_Lean_instReprLeanOption_repr___redArg(v_head_672_);
v___x_680_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_680_, 0, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v_x_670_ = v___x_680_;
v_x_671_ = v_tail_673_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_686_) == 0)
{
lean_dec(v_x_684_);
return v_x_685_;
}
else
{
lean_object* v_head_687_; lean_object* v_tail_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_698_; 
v_head_687_ = lean_ctor_get(v_x_686_, 0);
v_tail_688_ = lean_ctor_get(v_x_686_, 1);
v_isSharedCheck_698_ = !lean_is_exclusive(v_x_686_);
if (v_isSharedCheck_698_ == 0)
{
v___x_690_ = v_x_686_;
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_tail_688_);
lean_inc(v_head_687_);
lean_dec(v_x_686_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_698_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
lean_inc(v_x_684_);
if (v_isShared_691_ == 0)
{
lean_ctor_set_tag(v___x_690_, 5);
lean_ctor_set(v___x_690_, 1, v_x_684_);
lean_ctor_set(v___x_690_, 0, v_x_685_);
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_x_685_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v_x_684_);
v___x_693_ = v_reuseFailAlloc_697_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_instReprLeanOption_repr___redArg(v_head_687_);
v___x_695_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_693_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_684_, v___x_695_, v_tail_688_);
return v___x_696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object* v_x_699_, lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
lean_object* v___x_701_; 
lean_dec(v_x_700_);
v___x_701_ = lean_box(0);
return v___x_701_;
}
else
{
lean_object* v_tail_702_; 
v_tail_702_ = lean_ctor_get(v_x_699_, 1);
if (lean_obj_tag(v_tail_702_) == 0)
{
lean_object* v_head_703_; lean_object* v___x_704_; 
lean_dec(v_x_700_);
v_head_703_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_head_703_);
lean_dec_ref_known(v_x_699_, 2);
v___x_704_ = l_Lean_instReprLeanOption_repr___redArg(v_head_703_);
return v___x_704_;
}
else
{
lean_object* v_head_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc(v_tail_702_);
v_head_705_ = lean_ctor_get(v_x_699_, 0);
lean_inc(v_head_705_);
lean_dec_ref_known(v_x_699_, 2);
v___x_706_ = l_Lean_instReprLeanOption_repr___redArg(v_head_705_);
v___x_707_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_700_, v___x_706_, v_tail_702_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object* v_xs_708_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_array_get_size(v_xs_708_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_nat_dec_eq(v___x_709_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_712_ = lean_array_to_list(v_xs_708_);
v___x_713_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_714_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_712_, v___x_713_);
v___x_715_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_716_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_717_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_714_);
v___x_718_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_717_);
lean_ctor_set(v___x_719_, 1, v___x_718_);
v___x_720_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_715_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = l_Std_Format_fill(v___x_720_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
lean_dec_ref(v_xs_708_);
v___x_722_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
if (lean_obj_tag(v_x_725_) == 0)
{
lean_dec(v_x_723_);
return v_x_724_;
}
else
{
lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_738_; 
v_head_726_ = lean_ctor_get(v_x_725_, 0);
v_tail_727_ = lean_ctor_get(v_x_725_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_725_);
if (v_isSharedCheck_738_ == 0)
{
v___x_729_ = v_x_725_;
v_isShared_730_ = v_isSharedCheck_738_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_tail_727_);
lean_inc(v_head_726_);
lean_dec(v_x_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_738_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
lean_inc(v_x_723_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 5);
lean_ctor_set(v___x_729_, 1, v_x_723_);
lean_ctor_set(v___x_729_, 0, v_x_724_);
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_x_724_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_x_723_);
v___x_732_ = v_reuseFailAlloc_737_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = l_Lake_Target_repr___redArg(v_head_726_, v___x_733_);
v___x_735_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_732_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v_x_724_ = v___x_735_;
v_x_725_ = v_tail_727_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object* v_x_739_, lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_741_) == 0)
{
lean_dec(v_x_739_);
return v_x_740_;
}
else
{
lean_object* v_head_742_; lean_object* v_tail_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_754_; 
v_head_742_ = lean_ctor_get(v_x_741_, 0);
v_tail_743_ = lean_ctor_get(v_x_741_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_754_ == 0)
{
v___x_745_ = v_x_741_;
v_isShared_746_ = v_isSharedCheck_754_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_tail_743_);
lean_inc(v_head_742_);
lean_dec(v_x_741_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_754_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
lean_inc(v_x_739_);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 5);
lean_ctor_set(v___x_745_, 1, v_x_739_);
lean_ctor_set(v___x_745_, 0, v_x_740_);
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_x_740_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v_x_739_);
v___x_748_ = v_reuseFailAlloc_753_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = l_Lake_Target_repr___redArg(v_head_742_, v___x_749_);
v___x_751_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_748_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_739_, v___x_751_, v_tail_743_);
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
if (lean_obj_tag(v_x_755_) == 0)
{
lean_object* v___x_757_; 
lean_dec(v_x_756_);
v___x_757_ = lean_box(0);
return v___x_757_;
}
else
{
lean_object* v_tail_758_; 
v_tail_758_ = lean_ctor_get(v_x_755_, 1);
if (lean_obj_tag(v_tail_758_) == 0)
{
lean_object* v_head_759_; lean_object* v___x_760_; 
lean_dec(v_x_756_);
v_head_759_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_head_759_);
lean_dec_ref_known(v_x_755_, 2);
v___x_760_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_759_);
return v___x_760_;
}
else
{
lean_object* v_head_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
lean_inc(v_tail_758_);
v_head_761_ = lean_ctor_get(v_x_755_, 0);
lean_inc(v_head_761_);
lean_dec_ref_known(v_x_755_, 2);
v___x_762_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_761_);
v___x_763_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_756_, v___x_762_, v_tail_758_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object* v_xs_764_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_array_get_size(v_xs_764_);
v___x_766_ = lean_unsigned_to_nat(0u);
v___x_767_ = lean_nat_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_768_ = lean_array_to_list(v_xs_764_);
v___x_769_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_770_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_768_, v___x_769_);
v___x_771_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_772_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_773_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_770_);
v___x_774_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_771_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Std_Format_fill(v___x_776_);
return v___x_777_;
}
else
{
lean_object* v___x_778_; 
lean_dec_ref(v_xs_764_);
v___x_778_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_778_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_unsigned_to_nat(13u);
v___x_793_ = lean_nat_to_int(v___x_792_);
return v___x_793_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_unsigned_to_nat(15u);
v___x_798_ = lean_nat_to_int(v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(16u);
v___x_803_ = lean_nat_to_int(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_unsigned_to_nat(17u);
v___x_811_ = lean_nat_to_int(v___x_810_);
return v___x_811_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(21u);
v___x_816_ = lean_nat_to_int(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(11u);
v___x_836_ = lean_nat_to_int(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(23u);
v___x_841_ = lean_nat_to_int(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = lean_unsigned_to_nat(24u);
v___x_852_ = lean_nat_to_int(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__47(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(19u);
v___x_857_ = lean_nat_to_int(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_860_ = lean_string_length(v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__50(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__49, &l_Lake_instReprLeanConfig_repr___redArg___closed__49_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49);
v___x_862_ = lean_nat_to_int(v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_867_){
_start:
{
uint8_t v_buildType_868_; lean_object* v_leanOptions_869_; lean_object* v_moreLeanArgs_870_; lean_object* v_weakLeanArgs_871_; lean_object* v_moreLeancArgs_872_; lean_object* v_moreServerOptions_873_; lean_object* v_weakLeancArgs_874_; lean_object* v_moreLinkObjs_875_; lean_object* v_moreLinkLibs_876_; lean_object* v_moreLinkArgs_877_; lean_object* v_weakLinkArgs_878_; uint8_t v_backend_879_; lean_object* v_platformIndependent_880_; lean_object* v_dynlibs_881_; lean_object* v_plugins_882_; uint8_t v_requiresModuleSystem_883_; uint8_t v_allowNonModules_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_buildType_868_ = lean_ctor_get_uint8(v_x_867_, sizeof(void*)*13);
v_leanOptions_869_ = lean_ctor_get(v_x_867_, 0);
lean_inc_ref(v_leanOptions_869_);
v_moreLeanArgs_870_ = lean_ctor_get(v_x_867_, 1);
lean_inc_ref(v_moreLeanArgs_870_);
v_weakLeanArgs_871_ = lean_ctor_get(v_x_867_, 2);
lean_inc_ref(v_weakLeanArgs_871_);
v_moreLeancArgs_872_ = lean_ctor_get(v_x_867_, 3);
lean_inc_ref(v_moreLeancArgs_872_);
v_moreServerOptions_873_ = lean_ctor_get(v_x_867_, 4);
lean_inc_ref(v_moreServerOptions_873_);
v_weakLeancArgs_874_ = lean_ctor_get(v_x_867_, 5);
lean_inc_ref(v_weakLeancArgs_874_);
v_moreLinkObjs_875_ = lean_ctor_get(v_x_867_, 6);
lean_inc_ref(v_moreLinkObjs_875_);
v_moreLinkLibs_876_ = lean_ctor_get(v_x_867_, 7);
lean_inc_ref(v_moreLinkLibs_876_);
v_moreLinkArgs_877_ = lean_ctor_get(v_x_867_, 8);
lean_inc_ref(v_moreLinkArgs_877_);
v_weakLinkArgs_878_ = lean_ctor_get(v_x_867_, 9);
lean_inc_ref(v_weakLinkArgs_878_);
v_backend_879_ = lean_ctor_get_uint8(v_x_867_, sizeof(void*)*13 + 1);
v_platformIndependent_880_ = lean_ctor_get(v_x_867_, 10);
lean_inc(v_platformIndependent_880_);
v_dynlibs_881_ = lean_ctor_get(v_x_867_, 11);
lean_inc_ref(v_dynlibs_881_);
v_plugins_882_ = lean_ctor_get(v_x_867_, 12);
lean_inc_ref(v_plugins_882_);
v_requiresModuleSystem_883_ = lean_ctor_get_uint8(v_x_867_, sizeof(void*)*13 + 2);
v_allowNonModules_884_ = lean_ctor_get_uint8(v_x_867_, sizeof(void*)*13 + 3);
lean_dec_ref(v_x_867_);
v___x_885_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_886_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_887_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = l_Lake_instReprBuildType_repr(v_buildType_868_, v___x_888_);
v___x_890_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_887_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = 0;
v___x_892_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*1, v___x_891_);
v___x_893_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_886_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2));
v___x_895_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_box(1);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___x_898_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__9));
v___x_899_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_897_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_885_);
v___x_901_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__10, &l_Lake_instReprLeanConfig_repr___redArg___closed__10_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10);
v___x_902_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_869_);
v___x_903_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*1, v___x_891_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_900_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_894_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_896_);
v___x_908_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__12));
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v___x_885_);
v___x_911_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__13, &l_Lake_instReprLeanConfig_repr___redArg___closed__13_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13);
v___x_912_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_870_);
v___x_913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*1, v___x_891_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_910_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_894_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_896_);
v___x_918_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__15));
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_885_);
v___x_921_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_871_);
v___x_922_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_911_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set_uint8(v___x_923_, sizeof(void*)*1, v___x_891_);
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_920_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_894_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_896_);
v___x_927_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__17));
v___x_928_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_885_);
v___x_930_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__18, &l_Lake_instReprLeanConfig_repr___redArg___closed__18_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18);
v___x_931_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_872_);
v___x_932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_930_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v___x_891_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_929_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_894_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_896_);
v___x_937_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__20));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_885_);
v___x_940_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__21, &l_Lake_instReprLeanConfig_repr___redArg___closed__21_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21);
v___x_941_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_873_);
v___x_942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_891_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_894_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_896_);
v___x_947_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__23));
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_885_);
v___x_950_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_874_);
v___x_951_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_930_);
lean_ctor_set(v___x_951_, 1, v___x_950_);
v___x_952_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set_uint8(v___x_952_, sizeof(void*)*1, v___x_891_);
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_949_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_894_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_896_);
v___x_956_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__25));
v___x_957_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_885_);
v___x_959_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_875_);
v___x_960_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_911_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set_uint8(v___x_961_, sizeof(void*)*1, v___x_891_);
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_958_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_894_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_896_);
v___x_965_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__27));
v___x_966_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v___x_885_);
v___x_968_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_876_);
v___x_969_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_911_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set_uint8(v___x_970_, sizeof(void*)*1, v___x_891_);
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_967_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_894_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_896_);
v___x_974_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__29));
v___x_975_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_973_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_885_);
v___x_977_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_877_);
v___x_978_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_911_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set_uint8(v___x_979_, sizeof(void*)*1, v___x_891_);
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_976_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_894_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_896_);
v___x_983_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__31));
v___x_984_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v___x_885_);
v___x_986_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_878_);
v___x_987_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_911_);
lean_ctor_set(v___x_987_, 1, v___x_986_);
v___x_988_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set_uint8(v___x_988_, sizeof(void*)*1, v___x_891_);
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_985_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_894_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_896_);
v___x_992_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__33));
v___x_993_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v___x_885_);
v___x_995_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__34, &l_Lake_instReprLeanConfig_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34);
v___x_996_ = l_Lake_instReprBackend_repr(v_backend_879_, v___x_888_);
v___x_997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*1, v___x_891_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_894_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_896_);
v___x_1002_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__36));
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_885_);
v___x_1005_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__37, &l_Lake_instReprLeanConfig_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37);
v___x_1006_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_880_, v___x_888_);
lean_dec(v_platformIndependent_880_);
v___x_1007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*1, v___x_891_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1004_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_894_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_896_);
v___x_1012_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__39));
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_885_);
v___x_1015_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_881_);
v___x_1016_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_995_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*1, v___x_891_);
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1014_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_894_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_896_);
v___x_1021_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__41));
v___x_1022_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_885_);
v___x_1024_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_882_);
v___x_1025_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_995_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1026_, 0, v___x_1025_);
lean_ctor_set_uint8(v___x_1026_, sizeof(void*)*1, v___x_891_);
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1023_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_894_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_896_);
v___x_1030_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__43));
v___x_1031_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_885_);
v___x_1033_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__44, &l_Lake_instReprLeanConfig_repr___redArg___closed__44_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44);
v___x_1034_ = l_Bool_repr___redArg(v_requiresModuleSystem_883_);
v___x_1035_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*1, v___x_891_);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1032_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_894_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_896_);
v___x_1040_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__46));
v___x_1041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_885_);
v___x_1043_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__47, &l_Lake_instReprLeanConfig_repr___redArg___closed__47_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__47);
v___x_1044_ = l_Bool_repr___redArg(v_allowNonModules_884_);
v___x_1045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*1, v___x_891_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1042_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__50, &l_Lake_instReprLeanConfig_repr___redArg___closed__50_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__50);
v___x_1049_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__51));
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_1047_);
v___x_1051_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__52));
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1048_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set_uint8(v___x_1054_, sizeof(void*)*1, v___x_891_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1055_, lean_object* v_prec_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1058_, lean_object* v_prec_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lake_instReprLeanConfig_repr(v_x_1058_, v_prec_1059_);
lean_dec(v_prec_1059_);
return v_res_1060_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1063_){
_start:
{
uint8_t v_buildType_1064_; 
v_buildType_1064_ = lean_ctor_get_uint8(v_cfg_1063_, sizeof(void*)*13);
return v_buildType_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1065_){
_start:
{
uint8_t v_res_1066_; lean_object* v_r_1067_; 
v_res_1066_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1065_);
lean_dec_ref(v_cfg_1065_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1068_, lean_object* v_cfg_1069_){
_start:
{
lean_object* v_leanOptions_1070_; lean_object* v_moreLeanArgs_1071_; lean_object* v_weakLeanArgs_1072_; lean_object* v_moreLeancArgs_1073_; lean_object* v_moreServerOptions_1074_; lean_object* v_weakLeancArgs_1075_; lean_object* v_moreLinkObjs_1076_; lean_object* v_moreLinkLibs_1077_; lean_object* v_moreLinkArgs_1078_; lean_object* v_weakLinkArgs_1079_; uint8_t v_backend_1080_; lean_object* v_platformIndependent_1081_; lean_object* v_dynlibs_1082_; lean_object* v_plugins_1083_; uint8_t v_requiresModuleSystem_1084_; uint8_t v_allowNonModules_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_leanOptions_1070_ = lean_ctor_get(v_cfg_1069_, 0);
v_moreLeanArgs_1071_ = lean_ctor_get(v_cfg_1069_, 1);
v_weakLeanArgs_1072_ = lean_ctor_get(v_cfg_1069_, 2);
v_moreLeancArgs_1073_ = lean_ctor_get(v_cfg_1069_, 3);
v_moreServerOptions_1074_ = lean_ctor_get(v_cfg_1069_, 4);
v_weakLeancArgs_1075_ = lean_ctor_get(v_cfg_1069_, 5);
v_moreLinkObjs_1076_ = lean_ctor_get(v_cfg_1069_, 6);
v_moreLinkLibs_1077_ = lean_ctor_get(v_cfg_1069_, 7);
v_moreLinkArgs_1078_ = lean_ctor_get(v_cfg_1069_, 8);
v_weakLinkArgs_1079_ = lean_ctor_get(v_cfg_1069_, 9);
v_backend_1080_ = lean_ctor_get_uint8(v_cfg_1069_, sizeof(void*)*13 + 1);
v_platformIndependent_1081_ = lean_ctor_get(v_cfg_1069_, 10);
v_dynlibs_1082_ = lean_ctor_get(v_cfg_1069_, 11);
v_plugins_1083_ = lean_ctor_get(v_cfg_1069_, 12);
v_requiresModuleSystem_1084_ = lean_ctor_get_uint8(v_cfg_1069_, sizeof(void*)*13 + 2);
v_allowNonModules_1085_ = lean_ctor_get_uint8(v_cfg_1069_, sizeof(void*)*13 + 3);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_cfg_1069_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v_cfg_1069_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_plugins_1083_);
lean_inc(v_dynlibs_1082_);
lean_inc(v_platformIndependent_1081_);
lean_inc(v_weakLinkArgs_1079_);
lean_inc(v_moreLinkArgs_1078_);
lean_inc(v_moreLinkLibs_1077_);
lean_inc(v_moreLinkObjs_1076_);
lean_inc(v_weakLeancArgs_1075_);
lean_inc(v_moreServerOptions_1074_);
lean_inc(v_moreLeancArgs_1073_);
lean_inc(v_weakLeanArgs_1072_);
lean_inc(v_moreLeanArgs_1071_);
lean_inc(v_leanOptions_1070_);
lean_dec(v_cfg_1069_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_leanOptions_1070_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_moreLeanArgs_1071_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_weakLeanArgs_1072_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_moreLeancArgs_1073_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_moreServerOptions_1074_);
lean_ctor_set(v_reuseFailAlloc_1091_, 5, v_weakLeancArgs_1075_);
lean_ctor_set(v_reuseFailAlloc_1091_, 6, v_moreLinkObjs_1076_);
lean_ctor_set(v_reuseFailAlloc_1091_, 7, v_moreLinkLibs_1077_);
lean_ctor_set(v_reuseFailAlloc_1091_, 8, v_moreLinkArgs_1078_);
lean_ctor_set(v_reuseFailAlloc_1091_, 9, v_weakLinkArgs_1079_);
lean_ctor_set(v_reuseFailAlloc_1091_, 10, v_platformIndependent_1081_);
lean_ctor_set(v_reuseFailAlloc_1091_, 11, v_dynlibs_1082_);
lean_ctor_set(v_reuseFailAlloc_1091_, 12, v_plugins_1083_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*13 + 1, v_backend_1080_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1091_, sizeof(void*)*13 + 3, v_allowNonModules_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*13, v_val_1068_);
return v___x_1090_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1093_, lean_object* v_cfg_1094_){
_start:
{
uint8_t v_val_85__boxed_1095_; lean_object* v_res_1096_; 
v_val_85__boxed_1095_ = lean_unbox(v_val_1093_);
v_res_1096_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_85__boxed_1095_, v_cfg_1094_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1097_, lean_object* v_cfg_1098_){
_start:
{
uint8_t v_buildType_1099_; lean_object* v_leanOptions_1100_; lean_object* v_moreLeanArgs_1101_; lean_object* v_weakLeanArgs_1102_; lean_object* v_moreLeancArgs_1103_; lean_object* v_moreServerOptions_1104_; lean_object* v_weakLeancArgs_1105_; lean_object* v_moreLinkObjs_1106_; lean_object* v_moreLinkLibs_1107_; lean_object* v_moreLinkArgs_1108_; lean_object* v_weakLinkArgs_1109_; uint8_t v_backend_1110_; lean_object* v_platformIndependent_1111_; lean_object* v_dynlibs_1112_; lean_object* v_plugins_1113_; uint8_t v_requiresModuleSystem_1114_; uint8_t v_allowNonModules_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1125_; 
v_buildType_1099_ = lean_ctor_get_uint8(v_cfg_1098_, sizeof(void*)*13);
v_leanOptions_1100_ = lean_ctor_get(v_cfg_1098_, 0);
v_moreLeanArgs_1101_ = lean_ctor_get(v_cfg_1098_, 1);
v_weakLeanArgs_1102_ = lean_ctor_get(v_cfg_1098_, 2);
v_moreLeancArgs_1103_ = lean_ctor_get(v_cfg_1098_, 3);
v_moreServerOptions_1104_ = lean_ctor_get(v_cfg_1098_, 4);
v_weakLeancArgs_1105_ = lean_ctor_get(v_cfg_1098_, 5);
v_moreLinkObjs_1106_ = lean_ctor_get(v_cfg_1098_, 6);
v_moreLinkLibs_1107_ = lean_ctor_get(v_cfg_1098_, 7);
v_moreLinkArgs_1108_ = lean_ctor_get(v_cfg_1098_, 8);
v_weakLinkArgs_1109_ = lean_ctor_get(v_cfg_1098_, 9);
v_backend_1110_ = lean_ctor_get_uint8(v_cfg_1098_, sizeof(void*)*13 + 1);
v_platformIndependent_1111_ = lean_ctor_get(v_cfg_1098_, 10);
v_dynlibs_1112_ = lean_ctor_get(v_cfg_1098_, 11);
v_plugins_1113_ = lean_ctor_get(v_cfg_1098_, 12);
v_requiresModuleSystem_1114_ = lean_ctor_get_uint8(v_cfg_1098_, sizeof(void*)*13 + 2);
v_allowNonModules_1115_ = lean_ctor_get_uint8(v_cfg_1098_, sizeof(void*)*13 + 3);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_cfg_1098_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1117_ = v_cfg_1098_;
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_plugins_1113_);
lean_inc(v_dynlibs_1112_);
lean_inc(v_platformIndependent_1111_);
lean_inc(v_weakLinkArgs_1109_);
lean_inc(v_moreLinkArgs_1108_);
lean_inc(v_moreLinkLibs_1107_);
lean_inc(v_moreLinkObjs_1106_);
lean_inc(v_weakLeancArgs_1105_);
lean_inc(v_moreServerOptions_1104_);
lean_inc(v_moreLeancArgs_1103_);
lean_inc(v_weakLeanArgs_1102_);
lean_inc(v_moreLeanArgs_1101_);
lean_inc(v_leanOptions_1100_);
lean_dec(v_cfg_1098_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1125_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1119_ = lean_box(v_buildType_1099_);
v___x_1120_ = lean_apply_1(v_f_1097_, v___x_1119_);
if (v_isShared_1118_ == 0)
{
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_leanOptions_1100_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_moreLeanArgs_1101_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_weakLeanArgs_1102_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_moreLeancArgs_1103_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_moreServerOptions_1104_);
lean_ctor_set(v_reuseFailAlloc_1124_, 5, v_weakLeancArgs_1105_);
lean_ctor_set(v_reuseFailAlloc_1124_, 6, v_moreLinkObjs_1106_);
lean_ctor_set(v_reuseFailAlloc_1124_, 7, v_moreLinkLibs_1107_);
lean_ctor_set(v_reuseFailAlloc_1124_, 8, v_moreLinkArgs_1108_);
lean_ctor_set(v_reuseFailAlloc_1124_, 9, v_weakLinkArgs_1109_);
lean_ctor_set(v_reuseFailAlloc_1124_, 10, v_platformIndependent_1111_);
lean_ctor_set(v_reuseFailAlloc_1124_, 11, v_dynlibs_1112_);
lean_ctor_set(v_reuseFailAlloc_1124_, 12, v_plugins_1113_);
v___x_1122_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_unbox(v___x_1120_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*13, v___x_1123_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*13 + 1, v_backend_1110_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1114_);
lean_ctor_set_uint8(v___x_1122_, sizeof(void*)*13 + 3, v_allowNonModules_1115_);
return v___x_1122_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1126_){
_start:
{
uint8_t v___x_1127_; 
v___x_1127_ = 3;
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1128_){
_start:
{
uint8_t v_res_1129_; lean_object* v_r_1130_; 
v_res_1129_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1128_);
lean_dec_ref(v_x_1128_);
v_r_1130_ = lean_box(v_res_1129_);
return v_r_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1142_){
_start:
{
lean_object* v_leanOptions_1143_; 
v_leanOptions_1143_ = lean_ctor_get(v_cfg_1142_, 0);
lean_inc_ref(v_leanOptions_1143_);
return v_leanOptions_1143_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1144_);
lean_dec_ref(v_cfg_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1146_, lean_object* v_cfg_1147_){
_start:
{
uint8_t v_buildType_1148_; lean_object* v_moreLeanArgs_1149_; lean_object* v_weakLeanArgs_1150_; lean_object* v_moreLeancArgs_1151_; lean_object* v_moreServerOptions_1152_; lean_object* v_weakLeancArgs_1153_; lean_object* v_moreLinkObjs_1154_; lean_object* v_moreLinkLibs_1155_; lean_object* v_moreLinkArgs_1156_; lean_object* v_weakLinkArgs_1157_; uint8_t v_backend_1158_; lean_object* v_platformIndependent_1159_; lean_object* v_dynlibs_1160_; lean_object* v_plugins_1161_; uint8_t v_requiresModuleSystem_1162_; uint8_t v_allowNonModules_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_buildType_1148_ = lean_ctor_get_uint8(v_cfg_1147_, sizeof(void*)*13);
v_moreLeanArgs_1149_ = lean_ctor_get(v_cfg_1147_, 1);
v_weakLeanArgs_1150_ = lean_ctor_get(v_cfg_1147_, 2);
v_moreLeancArgs_1151_ = lean_ctor_get(v_cfg_1147_, 3);
v_moreServerOptions_1152_ = lean_ctor_get(v_cfg_1147_, 4);
v_weakLeancArgs_1153_ = lean_ctor_get(v_cfg_1147_, 5);
v_moreLinkObjs_1154_ = lean_ctor_get(v_cfg_1147_, 6);
v_moreLinkLibs_1155_ = lean_ctor_get(v_cfg_1147_, 7);
v_moreLinkArgs_1156_ = lean_ctor_get(v_cfg_1147_, 8);
v_weakLinkArgs_1157_ = lean_ctor_get(v_cfg_1147_, 9);
v_backend_1158_ = lean_ctor_get_uint8(v_cfg_1147_, sizeof(void*)*13 + 1);
v_platformIndependent_1159_ = lean_ctor_get(v_cfg_1147_, 10);
v_dynlibs_1160_ = lean_ctor_get(v_cfg_1147_, 11);
v_plugins_1161_ = lean_ctor_get(v_cfg_1147_, 12);
v_requiresModuleSystem_1162_ = lean_ctor_get_uint8(v_cfg_1147_, sizeof(void*)*13 + 2);
v_allowNonModules_1163_ = lean_ctor_get_uint8(v_cfg_1147_, sizeof(void*)*13 + 3);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_cfg_1147_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; 
v_unused_1171_ = lean_ctor_get(v_cfg_1147_, 0);
lean_dec(v_unused_1171_);
v___x_1165_ = v_cfg_1147_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_plugins_1161_);
lean_inc(v_dynlibs_1160_);
lean_inc(v_platformIndependent_1159_);
lean_inc(v_weakLinkArgs_1157_);
lean_inc(v_moreLinkArgs_1156_);
lean_inc(v_moreLinkLibs_1155_);
lean_inc(v_moreLinkObjs_1154_);
lean_inc(v_weakLeancArgs_1153_);
lean_inc(v_moreServerOptions_1152_);
lean_inc(v_moreLeancArgs_1151_);
lean_inc(v_weakLeanArgs_1150_);
lean_inc(v_moreLeanArgs_1149_);
lean_dec(v_cfg_1147_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v_val_1146_);
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_val_1146_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_moreLeanArgs_1149_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_weakLeanArgs_1150_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_moreLeancArgs_1151_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_moreServerOptions_1152_);
lean_ctor_set(v_reuseFailAlloc_1169_, 5, v_weakLeancArgs_1153_);
lean_ctor_set(v_reuseFailAlloc_1169_, 6, v_moreLinkObjs_1154_);
lean_ctor_set(v_reuseFailAlloc_1169_, 7, v_moreLinkLibs_1155_);
lean_ctor_set(v_reuseFailAlloc_1169_, 8, v_moreLinkArgs_1156_);
lean_ctor_set(v_reuseFailAlloc_1169_, 9, v_weakLinkArgs_1157_);
lean_ctor_set(v_reuseFailAlloc_1169_, 10, v_platformIndependent_1159_);
lean_ctor_set(v_reuseFailAlloc_1169_, 11, v_dynlibs_1160_);
lean_ctor_set(v_reuseFailAlloc_1169_, 12, v_plugins_1161_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*13, v_buildType_1148_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*13 + 1, v_backend_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1162_);
lean_ctor_set_uint8(v_reuseFailAlloc_1169_, sizeof(void*)*13 + 3, v_allowNonModules_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1172_, lean_object* v_cfg_1173_){
_start:
{
uint8_t v_buildType_1174_; lean_object* v_leanOptions_1175_; lean_object* v_moreLeanArgs_1176_; lean_object* v_weakLeanArgs_1177_; lean_object* v_moreLeancArgs_1178_; lean_object* v_moreServerOptions_1179_; lean_object* v_weakLeancArgs_1180_; lean_object* v_moreLinkObjs_1181_; lean_object* v_moreLinkLibs_1182_; lean_object* v_moreLinkArgs_1183_; lean_object* v_weakLinkArgs_1184_; uint8_t v_backend_1185_; lean_object* v_platformIndependent_1186_; lean_object* v_dynlibs_1187_; lean_object* v_plugins_1188_; uint8_t v_requiresModuleSystem_1189_; uint8_t v_allowNonModules_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
v_buildType_1174_ = lean_ctor_get_uint8(v_cfg_1173_, sizeof(void*)*13);
v_leanOptions_1175_ = lean_ctor_get(v_cfg_1173_, 0);
v_moreLeanArgs_1176_ = lean_ctor_get(v_cfg_1173_, 1);
v_weakLeanArgs_1177_ = lean_ctor_get(v_cfg_1173_, 2);
v_moreLeancArgs_1178_ = lean_ctor_get(v_cfg_1173_, 3);
v_moreServerOptions_1179_ = lean_ctor_get(v_cfg_1173_, 4);
v_weakLeancArgs_1180_ = lean_ctor_get(v_cfg_1173_, 5);
v_moreLinkObjs_1181_ = lean_ctor_get(v_cfg_1173_, 6);
v_moreLinkLibs_1182_ = lean_ctor_get(v_cfg_1173_, 7);
v_moreLinkArgs_1183_ = lean_ctor_get(v_cfg_1173_, 8);
v_weakLinkArgs_1184_ = lean_ctor_get(v_cfg_1173_, 9);
v_backend_1185_ = lean_ctor_get_uint8(v_cfg_1173_, sizeof(void*)*13 + 1);
v_platformIndependent_1186_ = lean_ctor_get(v_cfg_1173_, 10);
v_dynlibs_1187_ = lean_ctor_get(v_cfg_1173_, 11);
v_plugins_1188_ = lean_ctor_get(v_cfg_1173_, 12);
v_requiresModuleSystem_1189_ = lean_ctor_get_uint8(v_cfg_1173_, sizeof(void*)*13 + 2);
v_allowNonModules_1190_ = lean_ctor_get_uint8(v_cfg_1173_, sizeof(void*)*13 + 3);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_cfg_1173_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1192_ = v_cfg_1173_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_plugins_1188_);
lean_inc(v_dynlibs_1187_);
lean_inc(v_platformIndependent_1186_);
lean_inc(v_weakLinkArgs_1184_);
lean_inc(v_moreLinkArgs_1183_);
lean_inc(v_moreLinkLibs_1182_);
lean_inc(v_moreLinkObjs_1181_);
lean_inc(v_weakLeancArgs_1180_);
lean_inc(v_moreServerOptions_1179_);
lean_inc(v_moreLeancArgs_1178_);
lean_inc(v_weakLeanArgs_1177_);
lean_inc(v_moreLeanArgs_1176_);
lean_inc(v_leanOptions_1175_);
lean_dec(v_cfg_1173_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = lean_apply_1(v_f_1172_, v_leanOptions_1175_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_moreLeanArgs_1176_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_weakLeanArgs_1177_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_moreLeancArgs_1178_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_moreServerOptions_1179_);
lean_ctor_set(v_reuseFailAlloc_1197_, 5, v_weakLeancArgs_1180_);
lean_ctor_set(v_reuseFailAlloc_1197_, 6, v_moreLinkObjs_1181_);
lean_ctor_set(v_reuseFailAlloc_1197_, 7, v_moreLinkLibs_1182_);
lean_ctor_set(v_reuseFailAlloc_1197_, 8, v_moreLinkArgs_1183_);
lean_ctor_set(v_reuseFailAlloc_1197_, 9, v_weakLinkArgs_1184_);
lean_ctor_set(v_reuseFailAlloc_1197_, 10, v_platformIndependent_1186_);
lean_ctor_set(v_reuseFailAlloc_1197_, 11, v_dynlibs_1187_);
lean_ctor_set(v_reuseFailAlloc_1197_, 12, v_plugins_1188_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*13, v_buildType_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*13 + 1, v_backend_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1197_, sizeof(void*)*13 + 3, v_allowNonModules_1190_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1201_);
lean_dec_ref(v_x_1201_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1214_){
_start:
{
lean_object* v_moreLeanArgs_1215_; 
v_moreLeanArgs_1215_ = lean_ctor_get(v_cfg_1214_, 1);
lean_inc_ref(v_moreLeanArgs_1215_);
return v_moreLeanArgs_1215_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1216_);
lean_dec_ref(v_cfg_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1218_, lean_object* v_cfg_1219_){
_start:
{
uint8_t v_buildType_1220_; lean_object* v_leanOptions_1221_; lean_object* v_weakLeanArgs_1222_; lean_object* v_moreLeancArgs_1223_; lean_object* v_moreServerOptions_1224_; lean_object* v_weakLeancArgs_1225_; lean_object* v_moreLinkObjs_1226_; lean_object* v_moreLinkLibs_1227_; lean_object* v_moreLinkArgs_1228_; lean_object* v_weakLinkArgs_1229_; uint8_t v_backend_1230_; lean_object* v_platformIndependent_1231_; lean_object* v_dynlibs_1232_; lean_object* v_plugins_1233_; uint8_t v_requiresModuleSystem_1234_; uint8_t v_allowNonModules_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_buildType_1220_ = lean_ctor_get_uint8(v_cfg_1219_, sizeof(void*)*13);
v_leanOptions_1221_ = lean_ctor_get(v_cfg_1219_, 0);
v_weakLeanArgs_1222_ = lean_ctor_get(v_cfg_1219_, 2);
v_moreLeancArgs_1223_ = lean_ctor_get(v_cfg_1219_, 3);
v_moreServerOptions_1224_ = lean_ctor_get(v_cfg_1219_, 4);
v_weakLeancArgs_1225_ = lean_ctor_get(v_cfg_1219_, 5);
v_moreLinkObjs_1226_ = lean_ctor_get(v_cfg_1219_, 6);
v_moreLinkLibs_1227_ = lean_ctor_get(v_cfg_1219_, 7);
v_moreLinkArgs_1228_ = lean_ctor_get(v_cfg_1219_, 8);
v_weakLinkArgs_1229_ = lean_ctor_get(v_cfg_1219_, 9);
v_backend_1230_ = lean_ctor_get_uint8(v_cfg_1219_, sizeof(void*)*13 + 1);
v_platformIndependent_1231_ = lean_ctor_get(v_cfg_1219_, 10);
v_dynlibs_1232_ = lean_ctor_get(v_cfg_1219_, 11);
v_plugins_1233_ = lean_ctor_get(v_cfg_1219_, 12);
v_requiresModuleSystem_1234_ = lean_ctor_get_uint8(v_cfg_1219_, sizeof(void*)*13 + 2);
v_allowNonModules_1235_ = lean_ctor_get_uint8(v_cfg_1219_, sizeof(void*)*13 + 3);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_cfg_1219_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v_cfg_1219_, 1);
lean_dec(v_unused_1243_);
v___x_1237_ = v_cfg_1219_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_plugins_1233_);
lean_inc(v_dynlibs_1232_);
lean_inc(v_platformIndependent_1231_);
lean_inc(v_weakLinkArgs_1229_);
lean_inc(v_moreLinkArgs_1228_);
lean_inc(v_moreLinkLibs_1227_);
lean_inc(v_moreLinkObjs_1226_);
lean_inc(v_weakLeancArgs_1225_);
lean_inc(v_moreServerOptions_1224_);
lean_inc(v_moreLeancArgs_1223_);
lean_inc(v_weakLeanArgs_1222_);
lean_inc(v_leanOptions_1221_);
lean_dec(v_cfg_1219_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_val_1218_);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_leanOptions_1221_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v_val_1218_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_weakLeanArgs_1222_);
lean_ctor_set(v_reuseFailAlloc_1241_, 3, v_moreLeancArgs_1223_);
lean_ctor_set(v_reuseFailAlloc_1241_, 4, v_moreServerOptions_1224_);
lean_ctor_set(v_reuseFailAlloc_1241_, 5, v_weakLeancArgs_1225_);
lean_ctor_set(v_reuseFailAlloc_1241_, 6, v_moreLinkObjs_1226_);
lean_ctor_set(v_reuseFailAlloc_1241_, 7, v_moreLinkLibs_1227_);
lean_ctor_set(v_reuseFailAlloc_1241_, 8, v_moreLinkArgs_1228_);
lean_ctor_set(v_reuseFailAlloc_1241_, 9, v_weakLinkArgs_1229_);
lean_ctor_set(v_reuseFailAlloc_1241_, 10, v_platformIndependent_1231_);
lean_ctor_set(v_reuseFailAlloc_1241_, 11, v_dynlibs_1232_);
lean_ctor_set(v_reuseFailAlloc_1241_, 12, v_plugins_1233_);
lean_ctor_set_uint8(v_reuseFailAlloc_1241_, sizeof(void*)*13, v_buildType_1220_);
lean_ctor_set_uint8(v_reuseFailAlloc_1241_, sizeof(void*)*13 + 1, v_backend_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1241_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1241_, sizeof(void*)*13 + 3, v_allowNonModules_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1244_, lean_object* v_cfg_1245_){
_start:
{
uint8_t v_buildType_1246_; lean_object* v_leanOptions_1247_; lean_object* v_moreLeanArgs_1248_; lean_object* v_weakLeanArgs_1249_; lean_object* v_moreLeancArgs_1250_; lean_object* v_moreServerOptions_1251_; lean_object* v_weakLeancArgs_1252_; lean_object* v_moreLinkObjs_1253_; lean_object* v_moreLinkLibs_1254_; lean_object* v_moreLinkArgs_1255_; lean_object* v_weakLinkArgs_1256_; uint8_t v_backend_1257_; lean_object* v_platformIndependent_1258_; lean_object* v_dynlibs_1259_; lean_object* v_plugins_1260_; uint8_t v_requiresModuleSystem_1261_; uint8_t v_allowNonModules_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1270_; 
v_buildType_1246_ = lean_ctor_get_uint8(v_cfg_1245_, sizeof(void*)*13);
v_leanOptions_1247_ = lean_ctor_get(v_cfg_1245_, 0);
v_moreLeanArgs_1248_ = lean_ctor_get(v_cfg_1245_, 1);
v_weakLeanArgs_1249_ = lean_ctor_get(v_cfg_1245_, 2);
v_moreLeancArgs_1250_ = lean_ctor_get(v_cfg_1245_, 3);
v_moreServerOptions_1251_ = lean_ctor_get(v_cfg_1245_, 4);
v_weakLeancArgs_1252_ = lean_ctor_get(v_cfg_1245_, 5);
v_moreLinkObjs_1253_ = lean_ctor_get(v_cfg_1245_, 6);
v_moreLinkLibs_1254_ = lean_ctor_get(v_cfg_1245_, 7);
v_moreLinkArgs_1255_ = lean_ctor_get(v_cfg_1245_, 8);
v_weakLinkArgs_1256_ = lean_ctor_get(v_cfg_1245_, 9);
v_backend_1257_ = lean_ctor_get_uint8(v_cfg_1245_, sizeof(void*)*13 + 1);
v_platformIndependent_1258_ = lean_ctor_get(v_cfg_1245_, 10);
v_dynlibs_1259_ = lean_ctor_get(v_cfg_1245_, 11);
v_plugins_1260_ = lean_ctor_get(v_cfg_1245_, 12);
v_requiresModuleSystem_1261_ = lean_ctor_get_uint8(v_cfg_1245_, sizeof(void*)*13 + 2);
v_allowNonModules_1262_ = lean_ctor_get_uint8(v_cfg_1245_, sizeof(void*)*13 + 3);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_cfg_1245_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1264_ = v_cfg_1245_;
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_plugins_1260_);
lean_inc(v_dynlibs_1259_);
lean_inc(v_platformIndependent_1258_);
lean_inc(v_weakLinkArgs_1256_);
lean_inc(v_moreLinkArgs_1255_);
lean_inc(v_moreLinkLibs_1254_);
lean_inc(v_moreLinkObjs_1253_);
lean_inc(v_weakLeancArgs_1252_);
lean_inc(v_moreServerOptions_1251_);
lean_inc(v_moreLeancArgs_1250_);
lean_inc(v_weakLeanArgs_1249_);
lean_inc(v_moreLeanArgs_1248_);
lean_inc(v_leanOptions_1247_);
lean_dec(v_cfg_1245_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1270_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1266_ = lean_apply_1(v_f_1244_, v_moreLeanArgs_1248_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1266_);
v___x_1268_ = v___x_1264_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_leanOptions_1247_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_weakLeanArgs_1249_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_moreLeancArgs_1250_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v_moreServerOptions_1251_);
lean_ctor_set(v_reuseFailAlloc_1269_, 5, v_weakLeancArgs_1252_);
lean_ctor_set(v_reuseFailAlloc_1269_, 6, v_moreLinkObjs_1253_);
lean_ctor_set(v_reuseFailAlloc_1269_, 7, v_moreLinkLibs_1254_);
lean_ctor_set(v_reuseFailAlloc_1269_, 8, v_moreLinkArgs_1255_);
lean_ctor_set(v_reuseFailAlloc_1269_, 9, v_weakLinkArgs_1256_);
lean_ctor_set(v_reuseFailAlloc_1269_, 10, v_platformIndependent_1258_);
lean_ctor_set(v_reuseFailAlloc_1269_, 11, v_dynlibs_1259_);
lean_ctor_set(v_reuseFailAlloc_1269_, 12, v_plugins_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13, v_buildType_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 1, v_backend_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1269_, sizeof(void*)*13 + 3, v_allowNonModules_1262_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1271_){
_start:
{
lean_object* v___x_1272_; 
v___x_1272_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1273_);
lean_dec_ref(v_x_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1286_){
_start:
{
lean_object* v_weakLeanArgs_1287_; 
v_weakLeanArgs_1287_ = lean_ctor_get(v_cfg_1286_, 2);
lean_inc_ref(v_weakLeanArgs_1287_);
return v_weakLeanArgs_1287_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1288_);
lean_dec_ref(v_cfg_1288_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1290_, lean_object* v_cfg_1291_){
_start:
{
uint8_t v_buildType_1292_; lean_object* v_leanOptions_1293_; lean_object* v_moreLeanArgs_1294_; lean_object* v_moreLeancArgs_1295_; lean_object* v_moreServerOptions_1296_; lean_object* v_weakLeancArgs_1297_; lean_object* v_moreLinkObjs_1298_; lean_object* v_moreLinkLibs_1299_; lean_object* v_moreLinkArgs_1300_; lean_object* v_weakLinkArgs_1301_; uint8_t v_backend_1302_; lean_object* v_platformIndependent_1303_; lean_object* v_dynlibs_1304_; lean_object* v_plugins_1305_; uint8_t v_requiresModuleSystem_1306_; uint8_t v_allowNonModules_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_buildType_1292_ = lean_ctor_get_uint8(v_cfg_1291_, sizeof(void*)*13);
v_leanOptions_1293_ = lean_ctor_get(v_cfg_1291_, 0);
v_moreLeanArgs_1294_ = lean_ctor_get(v_cfg_1291_, 1);
v_moreLeancArgs_1295_ = lean_ctor_get(v_cfg_1291_, 3);
v_moreServerOptions_1296_ = lean_ctor_get(v_cfg_1291_, 4);
v_weakLeancArgs_1297_ = lean_ctor_get(v_cfg_1291_, 5);
v_moreLinkObjs_1298_ = lean_ctor_get(v_cfg_1291_, 6);
v_moreLinkLibs_1299_ = lean_ctor_get(v_cfg_1291_, 7);
v_moreLinkArgs_1300_ = lean_ctor_get(v_cfg_1291_, 8);
v_weakLinkArgs_1301_ = lean_ctor_get(v_cfg_1291_, 9);
v_backend_1302_ = lean_ctor_get_uint8(v_cfg_1291_, sizeof(void*)*13 + 1);
v_platformIndependent_1303_ = lean_ctor_get(v_cfg_1291_, 10);
v_dynlibs_1304_ = lean_ctor_get(v_cfg_1291_, 11);
v_plugins_1305_ = lean_ctor_get(v_cfg_1291_, 12);
v_requiresModuleSystem_1306_ = lean_ctor_get_uint8(v_cfg_1291_, sizeof(void*)*13 + 2);
v_allowNonModules_1307_ = lean_ctor_get_uint8(v_cfg_1291_, sizeof(void*)*13 + 3);
v_isSharedCheck_1314_ = !lean_is_exclusive(v_cfg_1291_);
if (v_isSharedCheck_1314_ == 0)
{
lean_object* v_unused_1315_; 
v_unused_1315_ = lean_ctor_get(v_cfg_1291_, 2);
lean_dec(v_unused_1315_);
v___x_1309_ = v_cfg_1291_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_plugins_1305_);
lean_inc(v_dynlibs_1304_);
lean_inc(v_platformIndependent_1303_);
lean_inc(v_weakLinkArgs_1301_);
lean_inc(v_moreLinkArgs_1300_);
lean_inc(v_moreLinkLibs_1299_);
lean_inc(v_moreLinkObjs_1298_);
lean_inc(v_weakLeancArgs_1297_);
lean_inc(v_moreServerOptions_1296_);
lean_inc(v_moreLeancArgs_1295_);
lean_inc(v_moreLeanArgs_1294_);
lean_inc(v_leanOptions_1293_);
lean_dec(v_cfg_1291_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 2, v_val_1290_);
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_leanOptions_1293_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_moreLeanArgs_1294_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_val_1290_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v_moreLeancArgs_1295_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_moreServerOptions_1296_);
lean_ctor_set(v_reuseFailAlloc_1313_, 5, v_weakLeancArgs_1297_);
lean_ctor_set(v_reuseFailAlloc_1313_, 6, v_moreLinkObjs_1298_);
lean_ctor_set(v_reuseFailAlloc_1313_, 7, v_moreLinkLibs_1299_);
lean_ctor_set(v_reuseFailAlloc_1313_, 8, v_moreLinkArgs_1300_);
lean_ctor_set(v_reuseFailAlloc_1313_, 9, v_weakLinkArgs_1301_);
lean_ctor_set(v_reuseFailAlloc_1313_, 10, v_platformIndependent_1303_);
lean_ctor_set(v_reuseFailAlloc_1313_, 11, v_dynlibs_1304_);
lean_ctor_set(v_reuseFailAlloc_1313_, 12, v_plugins_1305_);
lean_ctor_set_uint8(v_reuseFailAlloc_1313_, sizeof(void*)*13, v_buildType_1292_);
lean_ctor_set_uint8(v_reuseFailAlloc_1313_, sizeof(void*)*13 + 1, v_backend_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1313_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1313_, sizeof(void*)*13 + 3, v_allowNonModules_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1316_, lean_object* v_cfg_1317_){
_start:
{
uint8_t v_buildType_1318_; lean_object* v_leanOptions_1319_; lean_object* v_moreLeanArgs_1320_; lean_object* v_weakLeanArgs_1321_; lean_object* v_moreLeancArgs_1322_; lean_object* v_moreServerOptions_1323_; lean_object* v_weakLeancArgs_1324_; lean_object* v_moreLinkObjs_1325_; lean_object* v_moreLinkLibs_1326_; lean_object* v_moreLinkArgs_1327_; lean_object* v_weakLinkArgs_1328_; uint8_t v_backend_1329_; lean_object* v_platformIndependent_1330_; lean_object* v_dynlibs_1331_; lean_object* v_plugins_1332_; uint8_t v_requiresModuleSystem_1333_; uint8_t v_allowNonModules_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1342_; 
v_buildType_1318_ = lean_ctor_get_uint8(v_cfg_1317_, sizeof(void*)*13);
v_leanOptions_1319_ = lean_ctor_get(v_cfg_1317_, 0);
v_moreLeanArgs_1320_ = lean_ctor_get(v_cfg_1317_, 1);
v_weakLeanArgs_1321_ = lean_ctor_get(v_cfg_1317_, 2);
v_moreLeancArgs_1322_ = lean_ctor_get(v_cfg_1317_, 3);
v_moreServerOptions_1323_ = lean_ctor_get(v_cfg_1317_, 4);
v_weakLeancArgs_1324_ = lean_ctor_get(v_cfg_1317_, 5);
v_moreLinkObjs_1325_ = lean_ctor_get(v_cfg_1317_, 6);
v_moreLinkLibs_1326_ = lean_ctor_get(v_cfg_1317_, 7);
v_moreLinkArgs_1327_ = lean_ctor_get(v_cfg_1317_, 8);
v_weakLinkArgs_1328_ = lean_ctor_get(v_cfg_1317_, 9);
v_backend_1329_ = lean_ctor_get_uint8(v_cfg_1317_, sizeof(void*)*13 + 1);
v_platformIndependent_1330_ = lean_ctor_get(v_cfg_1317_, 10);
v_dynlibs_1331_ = lean_ctor_get(v_cfg_1317_, 11);
v_plugins_1332_ = lean_ctor_get(v_cfg_1317_, 12);
v_requiresModuleSystem_1333_ = lean_ctor_get_uint8(v_cfg_1317_, sizeof(void*)*13 + 2);
v_allowNonModules_1334_ = lean_ctor_get_uint8(v_cfg_1317_, sizeof(void*)*13 + 3);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_cfg_1317_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1336_ = v_cfg_1317_;
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_plugins_1332_);
lean_inc(v_dynlibs_1331_);
lean_inc(v_platformIndependent_1330_);
lean_inc(v_weakLinkArgs_1328_);
lean_inc(v_moreLinkArgs_1327_);
lean_inc(v_moreLinkLibs_1326_);
lean_inc(v_moreLinkObjs_1325_);
lean_inc(v_weakLeancArgs_1324_);
lean_inc(v_moreServerOptions_1323_);
lean_inc(v_moreLeancArgs_1322_);
lean_inc(v_weakLeanArgs_1321_);
lean_inc(v_moreLeanArgs_1320_);
lean_inc(v_leanOptions_1319_);
lean_dec(v_cfg_1317_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1342_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_apply_1(v_f_1316_, v_weakLeanArgs_1321_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 2, v___x_1338_);
v___x_1340_ = v___x_1336_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_leanOptions_1319_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_moreLeanArgs_1320_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_moreLeancArgs_1322_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_moreServerOptions_1323_);
lean_ctor_set(v_reuseFailAlloc_1341_, 5, v_weakLeancArgs_1324_);
lean_ctor_set(v_reuseFailAlloc_1341_, 6, v_moreLinkObjs_1325_);
lean_ctor_set(v_reuseFailAlloc_1341_, 7, v_moreLinkLibs_1326_);
lean_ctor_set(v_reuseFailAlloc_1341_, 8, v_moreLinkArgs_1327_);
lean_ctor_set(v_reuseFailAlloc_1341_, 9, v_weakLinkArgs_1328_);
lean_ctor_set(v_reuseFailAlloc_1341_, 10, v_platformIndependent_1330_);
lean_ctor_set(v_reuseFailAlloc_1341_, 11, v_dynlibs_1331_);
lean_ctor_set(v_reuseFailAlloc_1341_, 12, v_plugins_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13, v_buildType_1318_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13 + 1, v_backend_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1341_, sizeof(void*)*13 + 3, v_allowNonModules_1334_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1353_){
_start:
{
lean_object* v_moreLeancArgs_1354_; 
v_moreLeancArgs_1354_ = lean_ctor_get(v_cfg_1353_, 3);
lean_inc_ref(v_moreLeancArgs_1354_);
return v_moreLeancArgs_1354_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1355_);
lean_dec_ref(v_cfg_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1357_, lean_object* v_cfg_1358_){
_start:
{
uint8_t v_buildType_1359_; lean_object* v_leanOptions_1360_; lean_object* v_moreLeanArgs_1361_; lean_object* v_weakLeanArgs_1362_; lean_object* v_moreServerOptions_1363_; lean_object* v_weakLeancArgs_1364_; lean_object* v_moreLinkObjs_1365_; lean_object* v_moreLinkLibs_1366_; lean_object* v_moreLinkArgs_1367_; lean_object* v_weakLinkArgs_1368_; uint8_t v_backend_1369_; lean_object* v_platformIndependent_1370_; lean_object* v_dynlibs_1371_; lean_object* v_plugins_1372_; uint8_t v_requiresModuleSystem_1373_; uint8_t v_allowNonModules_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
v_buildType_1359_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*13);
v_leanOptions_1360_ = lean_ctor_get(v_cfg_1358_, 0);
v_moreLeanArgs_1361_ = lean_ctor_get(v_cfg_1358_, 1);
v_weakLeanArgs_1362_ = lean_ctor_get(v_cfg_1358_, 2);
v_moreServerOptions_1363_ = lean_ctor_get(v_cfg_1358_, 4);
v_weakLeancArgs_1364_ = lean_ctor_get(v_cfg_1358_, 5);
v_moreLinkObjs_1365_ = lean_ctor_get(v_cfg_1358_, 6);
v_moreLinkLibs_1366_ = lean_ctor_get(v_cfg_1358_, 7);
v_moreLinkArgs_1367_ = lean_ctor_get(v_cfg_1358_, 8);
v_weakLinkArgs_1368_ = lean_ctor_get(v_cfg_1358_, 9);
v_backend_1369_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*13 + 1);
v_platformIndependent_1370_ = lean_ctor_get(v_cfg_1358_, 10);
v_dynlibs_1371_ = lean_ctor_get(v_cfg_1358_, 11);
v_plugins_1372_ = lean_ctor_get(v_cfg_1358_, 12);
v_requiresModuleSystem_1373_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*13 + 2);
v_allowNonModules_1374_ = lean_ctor_get_uint8(v_cfg_1358_, sizeof(void*)*13 + 3);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_cfg_1358_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v_cfg_1358_, 3);
lean_dec(v_unused_1382_);
v___x_1376_ = v_cfg_1358_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_plugins_1372_);
lean_inc(v_dynlibs_1371_);
lean_inc(v_platformIndependent_1370_);
lean_inc(v_weakLinkArgs_1368_);
lean_inc(v_moreLinkArgs_1367_);
lean_inc(v_moreLinkLibs_1366_);
lean_inc(v_moreLinkObjs_1365_);
lean_inc(v_weakLeancArgs_1364_);
lean_inc(v_moreServerOptions_1363_);
lean_inc(v_weakLeanArgs_1362_);
lean_inc(v_moreLeanArgs_1361_);
lean_inc(v_leanOptions_1360_);
lean_dec(v_cfg_1358_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 3, v_val_1357_);
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_leanOptions_1360_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v_moreLeanArgs_1361_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_weakLeanArgs_1362_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_val_1357_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_moreServerOptions_1363_);
lean_ctor_set(v_reuseFailAlloc_1380_, 5, v_weakLeancArgs_1364_);
lean_ctor_set(v_reuseFailAlloc_1380_, 6, v_moreLinkObjs_1365_);
lean_ctor_set(v_reuseFailAlloc_1380_, 7, v_moreLinkLibs_1366_);
lean_ctor_set(v_reuseFailAlloc_1380_, 8, v_moreLinkArgs_1367_);
lean_ctor_set(v_reuseFailAlloc_1380_, 9, v_weakLinkArgs_1368_);
lean_ctor_set(v_reuseFailAlloc_1380_, 10, v_platformIndependent_1370_);
lean_ctor_set(v_reuseFailAlloc_1380_, 11, v_dynlibs_1371_);
lean_ctor_set(v_reuseFailAlloc_1380_, 12, v_plugins_1372_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*13, v_buildType_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*13 + 1, v_backend_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1373_);
lean_ctor_set_uint8(v_reuseFailAlloc_1380_, sizeof(void*)*13 + 3, v_allowNonModules_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1383_, lean_object* v_cfg_1384_){
_start:
{
uint8_t v_buildType_1385_; lean_object* v_leanOptions_1386_; lean_object* v_moreLeanArgs_1387_; lean_object* v_weakLeanArgs_1388_; lean_object* v_moreLeancArgs_1389_; lean_object* v_moreServerOptions_1390_; lean_object* v_weakLeancArgs_1391_; lean_object* v_moreLinkObjs_1392_; lean_object* v_moreLinkLibs_1393_; lean_object* v_moreLinkArgs_1394_; lean_object* v_weakLinkArgs_1395_; uint8_t v_backend_1396_; lean_object* v_platformIndependent_1397_; lean_object* v_dynlibs_1398_; lean_object* v_plugins_1399_; uint8_t v_requiresModuleSystem_1400_; uint8_t v_allowNonModules_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1409_; 
v_buildType_1385_ = lean_ctor_get_uint8(v_cfg_1384_, sizeof(void*)*13);
v_leanOptions_1386_ = lean_ctor_get(v_cfg_1384_, 0);
v_moreLeanArgs_1387_ = lean_ctor_get(v_cfg_1384_, 1);
v_weakLeanArgs_1388_ = lean_ctor_get(v_cfg_1384_, 2);
v_moreLeancArgs_1389_ = lean_ctor_get(v_cfg_1384_, 3);
v_moreServerOptions_1390_ = lean_ctor_get(v_cfg_1384_, 4);
v_weakLeancArgs_1391_ = lean_ctor_get(v_cfg_1384_, 5);
v_moreLinkObjs_1392_ = lean_ctor_get(v_cfg_1384_, 6);
v_moreLinkLibs_1393_ = lean_ctor_get(v_cfg_1384_, 7);
v_moreLinkArgs_1394_ = lean_ctor_get(v_cfg_1384_, 8);
v_weakLinkArgs_1395_ = lean_ctor_get(v_cfg_1384_, 9);
v_backend_1396_ = lean_ctor_get_uint8(v_cfg_1384_, sizeof(void*)*13 + 1);
v_platformIndependent_1397_ = lean_ctor_get(v_cfg_1384_, 10);
v_dynlibs_1398_ = lean_ctor_get(v_cfg_1384_, 11);
v_plugins_1399_ = lean_ctor_get(v_cfg_1384_, 12);
v_requiresModuleSystem_1400_ = lean_ctor_get_uint8(v_cfg_1384_, sizeof(void*)*13 + 2);
v_allowNonModules_1401_ = lean_ctor_get_uint8(v_cfg_1384_, sizeof(void*)*13 + 3);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_cfg_1384_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1403_ = v_cfg_1384_;
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_plugins_1399_);
lean_inc(v_dynlibs_1398_);
lean_inc(v_platformIndependent_1397_);
lean_inc(v_weakLinkArgs_1395_);
lean_inc(v_moreLinkArgs_1394_);
lean_inc(v_moreLinkLibs_1393_);
lean_inc(v_moreLinkObjs_1392_);
lean_inc(v_weakLeancArgs_1391_);
lean_inc(v_moreServerOptions_1390_);
lean_inc(v_moreLeancArgs_1389_);
lean_inc(v_weakLeanArgs_1388_);
lean_inc(v_moreLeanArgs_1387_);
lean_inc(v_leanOptions_1386_);
lean_dec(v_cfg_1384_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1409_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1405_ = lean_apply_1(v_f_1383_, v_moreLeancArgs_1389_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 3, v___x_1405_);
v___x_1407_ = v___x_1403_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_leanOptions_1386_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_moreLeanArgs_1387_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_weakLeanArgs_1388_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_moreServerOptions_1390_);
lean_ctor_set(v_reuseFailAlloc_1408_, 5, v_weakLeancArgs_1391_);
lean_ctor_set(v_reuseFailAlloc_1408_, 6, v_moreLinkObjs_1392_);
lean_ctor_set(v_reuseFailAlloc_1408_, 7, v_moreLinkLibs_1393_);
lean_ctor_set(v_reuseFailAlloc_1408_, 8, v_moreLinkArgs_1394_);
lean_ctor_set(v_reuseFailAlloc_1408_, 9, v_weakLinkArgs_1395_);
lean_ctor_set(v_reuseFailAlloc_1408_, 10, v_platformIndependent_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 11, v_dynlibs_1398_);
lean_ctor_set(v_reuseFailAlloc_1408_, 12, v_plugins_1399_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13, v_buildType_1385_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13 + 1, v_backend_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13 + 3, v_allowNonModules_1401_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1420_){
_start:
{
lean_object* v_moreServerOptions_1421_; 
v_moreServerOptions_1421_ = lean_ctor_get(v_cfg_1420_, 4);
lean_inc_ref(v_moreServerOptions_1421_);
return v_moreServerOptions_1421_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1422_);
lean_dec_ref(v_cfg_1422_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1424_, lean_object* v_cfg_1425_){
_start:
{
uint8_t v_buildType_1426_; lean_object* v_leanOptions_1427_; lean_object* v_moreLeanArgs_1428_; lean_object* v_weakLeanArgs_1429_; lean_object* v_moreLeancArgs_1430_; lean_object* v_weakLeancArgs_1431_; lean_object* v_moreLinkObjs_1432_; lean_object* v_moreLinkLibs_1433_; lean_object* v_moreLinkArgs_1434_; lean_object* v_weakLinkArgs_1435_; uint8_t v_backend_1436_; lean_object* v_platformIndependent_1437_; lean_object* v_dynlibs_1438_; lean_object* v_plugins_1439_; uint8_t v_requiresModuleSystem_1440_; uint8_t v_allowNonModules_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_buildType_1426_ = lean_ctor_get_uint8(v_cfg_1425_, sizeof(void*)*13);
v_leanOptions_1427_ = lean_ctor_get(v_cfg_1425_, 0);
v_moreLeanArgs_1428_ = lean_ctor_get(v_cfg_1425_, 1);
v_weakLeanArgs_1429_ = lean_ctor_get(v_cfg_1425_, 2);
v_moreLeancArgs_1430_ = lean_ctor_get(v_cfg_1425_, 3);
v_weakLeancArgs_1431_ = lean_ctor_get(v_cfg_1425_, 5);
v_moreLinkObjs_1432_ = lean_ctor_get(v_cfg_1425_, 6);
v_moreLinkLibs_1433_ = lean_ctor_get(v_cfg_1425_, 7);
v_moreLinkArgs_1434_ = lean_ctor_get(v_cfg_1425_, 8);
v_weakLinkArgs_1435_ = lean_ctor_get(v_cfg_1425_, 9);
v_backend_1436_ = lean_ctor_get_uint8(v_cfg_1425_, sizeof(void*)*13 + 1);
v_platformIndependent_1437_ = lean_ctor_get(v_cfg_1425_, 10);
v_dynlibs_1438_ = lean_ctor_get(v_cfg_1425_, 11);
v_plugins_1439_ = lean_ctor_get(v_cfg_1425_, 12);
v_requiresModuleSystem_1440_ = lean_ctor_get_uint8(v_cfg_1425_, sizeof(void*)*13 + 2);
v_allowNonModules_1441_ = lean_ctor_get_uint8(v_cfg_1425_, sizeof(void*)*13 + 3);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_cfg_1425_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_cfg_1425_, 4);
lean_dec(v_unused_1449_);
v___x_1443_ = v_cfg_1425_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_plugins_1439_);
lean_inc(v_dynlibs_1438_);
lean_inc(v_platformIndependent_1437_);
lean_inc(v_weakLinkArgs_1435_);
lean_inc(v_moreLinkArgs_1434_);
lean_inc(v_moreLinkLibs_1433_);
lean_inc(v_moreLinkObjs_1432_);
lean_inc(v_weakLeancArgs_1431_);
lean_inc(v_moreLeancArgs_1430_);
lean_inc(v_weakLeanArgs_1429_);
lean_inc(v_moreLeanArgs_1428_);
lean_inc(v_leanOptions_1427_);
lean_dec(v_cfg_1425_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 4, v_val_1424_);
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_leanOptions_1427_);
lean_ctor_set(v_reuseFailAlloc_1447_, 1, v_moreLeanArgs_1428_);
lean_ctor_set(v_reuseFailAlloc_1447_, 2, v_weakLeanArgs_1429_);
lean_ctor_set(v_reuseFailAlloc_1447_, 3, v_moreLeancArgs_1430_);
lean_ctor_set(v_reuseFailAlloc_1447_, 4, v_val_1424_);
lean_ctor_set(v_reuseFailAlloc_1447_, 5, v_weakLeancArgs_1431_);
lean_ctor_set(v_reuseFailAlloc_1447_, 6, v_moreLinkObjs_1432_);
lean_ctor_set(v_reuseFailAlloc_1447_, 7, v_moreLinkLibs_1433_);
lean_ctor_set(v_reuseFailAlloc_1447_, 8, v_moreLinkArgs_1434_);
lean_ctor_set(v_reuseFailAlloc_1447_, 9, v_weakLinkArgs_1435_);
lean_ctor_set(v_reuseFailAlloc_1447_, 10, v_platformIndependent_1437_);
lean_ctor_set(v_reuseFailAlloc_1447_, 11, v_dynlibs_1438_);
lean_ctor_set(v_reuseFailAlloc_1447_, 12, v_plugins_1439_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*13, v_buildType_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*13 + 1, v_backend_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1447_, sizeof(void*)*13 + 3, v_allowNonModules_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1450_, lean_object* v_cfg_1451_){
_start:
{
uint8_t v_buildType_1452_; lean_object* v_leanOptions_1453_; lean_object* v_moreLeanArgs_1454_; lean_object* v_weakLeanArgs_1455_; lean_object* v_moreLeancArgs_1456_; lean_object* v_moreServerOptions_1457_; lean_object* v_weakLeancArgs_1458_; lean_object* v_moreLinkObjs_1459_; lean_object* v_moreLinkLibs_1460_; lean_object* v_moreLinkArgs_1461_; lean_object* v_weakLinkArgs_1462_; uint8_t v_backend_1463_; lean_object* v_platformIndependent_1464_; lean_object* v_dynlibs_1465_; lean_object* v_plugins_1466_; uint8_t v_requiresModuleSystem_1467_; uint8_t v_allowNonModules_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1476_; 
v_buildType_1452_ = lean_ctor_get_uint8(v_cfg_1451_, sizeof(void*)*13);
v_leanOptions_1453_ = lean_ctor_get(v_cfg_1451_, 0);
v_moreLeanArgs_1454_ = lean_ctor_get(v_cfg_1451_, 1);
v_weakLeanArgs_1455_ = lean_ctor_get(v_cfg_1451_, 2);
v_moreLeancArgs_1456_ = lean_ctor_get(v_cfg_1451_, 3);
v_moreServerOptions_1457_ = lean_ctor_get(v_cfg_1451_, 4);
v_weakLeancArgs_1458_ = lean_ctor_get(v_cfg_1451_, 5);
v_moreLinkObjs_1459_ = lean_ctor_get(v_cfg_1451_, 6);
v_moreLinkLibs_1460_ = lean_ctor_get(v_cfg_1451_, 7);
v_moreLinkArgs_1461_ = lean_ctor_get(v_cfg_1451_, 8);
v_weakLinkArgs_1462_ = lean_ctor_get(v_cfg_1451_, 9);
v_backend_1463_ = lean_ctor_get_uint8(v_cfg_1451_, sizeof(void*)*13 + 1);
v_platformIndependent_1464_ = lean_ctor_get(v_cfg_1451_, 10);
v_dynlibs_1465_ = lean_ctor_get(v_cfg_1451_, 11);
v_plugins_1466_ = lean_ctor_get(v_cfg_1451_, 12);
v_requiresModuleSystem_1467_ = lean_ctor_get_uint8(v_cfg_1451_, sizeof(void*)*13 + 2);
v_allowNonModules_1468_ = lean_ctor_get_uint8(v_cfg_1451_, sizeof(void*)*13 + 3);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_cfg_1451_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1470_ = v_cfg_1451_;
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_plugins_1466_);
lean_inc(v_dynlibs_1465_);
lean_inc(v_platformIndependent_1464_);
lean_inc(v_weakLinkArgs_1462_);
lean_inc(v_moreLinkArgs_1461_);
lean_inc(v_moreLinkLibs_1460_);
lean_inc(v_moreLinkObjs_1459_);
lean_inc(v_weakLeancArgs_1458_);
lean_inc(v_moreServerOptions_1457_);
lean_inc(v_moreLeancArgs_1456_);
lean_inc(v_weakLeanArgs_1455_);
lean_inc(v_moreLeanArgs_1454_);
lean_inc(v_leanOptions_1453_);
lean_dec(v_cfg_1451_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1476_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
v___x_1472_ = lean_apply_1(v_f_1450_, v_moreServerOptions_1457_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 4, v___x_1472_);
v___x_1474_ = v___x_1470_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_leanOptions_1453_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_moreLeanArgs_1454_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_weakLeanArgs_1455_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_moreLeancArgs_1456_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1475_, 5, v_weakLeancArgs_1458_);
lean_ctor_set(v_reuseFailAlloc_1475_, 6, v_moreLinkObjs_1459_);
lean_ctor_set(v_reuseFailAlloc_1475_, 7, v_moreLinkLibs_1460_);
lean_ctor_set(v_reuseFailAlloc_1475_, 8, v_moreLinkArgs_1461_);
lean_ctor_set(v_reuseFailAlloc_1475_, 9, v_weakLinkArgs_1462_);
lean_ctor_set(v_reuseFailAlloc_1475_, 10, v_platformIndependent_1464_);
lean_ctor_set(v_reuseFailAlloc_1475_, 11, v_dynlibs_1465_);
lean_ctor_set(v_reuseFailAlloc_1475_, 12, v_plugins_1466_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13, v_buildType_1452_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 1, v_backend_1463_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1475_, sizeof(void*)*13 + 3, v_allowNonModules_1468_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1487_){
_start:
{
lean_object* v_weakLeancArgs_1488_; 
v_weakLeancArgs_1488_ = lean_ctor_get(v_cfg_1487_, 5);
lean_inc_ref(v_weakLeancArgs_1488_);
return v_weakLeancArgs_1488_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1489_);
lean_dec_ref(v_cfg_1489_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1491_, lean_object* v_cfg_1492_){
_start:
{
uint8_t v_buildType_1493_; lean_object* v_leanOptions_1494_; lean_object* v_moreLeanArgs_1495_; lean_object* v_weakLeanArgs_1496_; lean_object* v_moreLeancArgs_1497_; lean_object* v_moreServerOptions_1498_; lean_object* v_moreLinkObjs_1499_; lean_object* v_moreLinkLibs_1500_; lean_object* v_moreLinkArgs_1501_; lean_object* v_weakLinkArgs_1502_; uint8_t v_backend_1503_; lean_object* v_platformIndependent_1504_; lean_object* v_dynlibs_1505_; lean_object* v_plugins_1506_; uint8_t v_requiresModuleSystem_1507_; uint8_t v_allowNonModules_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1515_; 
v_buildType_1493_ = lean_ctor_get_uint8(v_cfg_1492_, sizeof(void*)*13);
v_leanOptions_1494_ = lean_ctor_get(v_cfg_1492_, 0);
v_moreLeanArgs_1495_ = lean_ctor_get(v_cfg_1492_, 1);
v_weakLeanArgs_1496_ = lean_ctor_get(v_cfg_1492_, 2);
v_moreLeancArgs_1497_ = lean_ctor_get(v_cfg_1492_, 3);
v_moreServerOptions_1498_ = lean_ctor_get(v_cfg_1492_, 4);
v_moreLinkObjs_1499_ = lean_ctor_get(v_cfg_1492_, 6);
v_moreLinkLibs_1500_ = lean_ctor_get(v_cfg_1492_, 7);
v_moreLinkArgs_1501_ = lean_ctor_get(v_cfg_1492_, 8);
v_weakLinkArgs_1502_ = lean_ctor_get(v_cfg_1492_, 9);
v_backend_1503_ = lean_ctor_get_uint8(v_cfg_1492_, sizeof(void*)*13 + 1);
v_platformIndependent_1504_ = lean_ctor_get(v_cfg_1492_, 10);
v_dynlibs_1505_ = lean_ctor_get(v_cfg_1492_, 11);
v_plugins_1506_ = lean_ctor_get(v_cfg_1492_, 12);
v_requiresModuleSystem_1507_ = lean_ctor_get_uint8(v_cfg_1492_, sizeof(void*)*13 + 2);
v_allowNonModules_1508_ = lean_ctor_get_uint8(v_cfg_1492_, sizeof(void*)*13 + 3);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_cfg_1492_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_cfg_1492_, 5);
lean_dec(v_unused_1516_);
v___x_1510_ = v_cfg_1492_;
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_plugins_1506_);
lean_inc(v_dynlibs_1505_);
lean_inc(v_platformIndependent_1504_);
lean_inc(v_weakLinkArgs_1502_);
lean_inc(v_moreLinkArgs_1501_);
lean_inc(v_moreLinkLibs_1500_);
lean_inc(v_moreLinkObjs_1499_);
lean_inc(v_moreServerOptions_1498_);
lean_inc(v_moreLeancArgs_1497_);
lean_inc(v_weakLeanArgs_1496_);
lean_inc(v_moreLeanArgs_1495_);
lean_inc(v_leanOptions_1494_);
lean_dec(v_cfg_1492_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1515_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1513_; 
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 5, v_val_1491_);
v___x_1513_ = v___x_1510_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_leanOptions_1494_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_moreLeanArgs_1495_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_weakLeanArgs_1496_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_moreLeancArgs_1497_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_moreServerOptions_1498_);
lean_ctor_set(v_reuseFailAlloc_1514_, 5, v_val_1491_);
lean_ctor_set(v_reuseFailAlloc_1514_, 6, v_moreLinkObjs_1499_);
lean_ctor_set(v_reuseFailAlloc_1514_, 7, v_moreLinkLibs_1500_);
lean_ctor_set(v_reuseFailAlloc_1514_, 8, v_moreLinkArgs_1501_);
lean_ctor_set(v_reuseFailAlloc_1514_, 9, v_weakLinkArgs_1502_);
lean_ctor_set(v_reuseFailAlloc_1514_, 10, v_platformIndependent_1504_);
lean_ctor_set(v_reuseFailAlloc_1514_, 11, v_dynlibs_1505_);
lean_ctor_set(v_reuseFailAlloc_1514_, 12, v_plugins_1506_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*13, v_buildType_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*13 + 1, v_backend_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*13 + 3, v_allowNonModules_1508_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1517_, lean_object* v_cfg_1518_){
_start:
{
uint8_t v_buildType_1519_; lean_object* v_leanOptions_1520_; lean_object* v_moreLeanArgs_1521_; lean_object* v_weakLeanArgs_1522_; lean_object* v_moreLeancArgs_1523_; lean_object* v_moreServerOptions_1524_; lean_object* v_weakLeancArgs_1525_; lean_object* v_moreLinkObjs_1526_; lean_object* v_moreLinkLibs_1527_; lean_object* v_moreLinkArgs_1528_; lean_object* v_weakLinkArgs_1529_; uint8_t v_backend_1530_; lean_object* v_platformIndependent_1531_; lean_object* v_dynlibs_1532_; lean_object* v_plugins_1533_; uint8_t v_requiresModuleSystem_1534_; uint8_t v_allowNonModules_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1543_; 
v_buildType_1519_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13);
v_leanOptions_1520_ = lean_ctor_get(v_cfg_1518_, 0);
v_moreLeanArgs_1521_ = lean_ctor_get(v_cfg_1518_, 1);
v_weakLeanArgs_1522_ = lean_ctor_get(v_cfg_1518_, 2);
v_moreLeancArgs_1523_ = lean_ctor_get(v_cfg_1518_, 3);
v_moreServerOptions_1524_ = lean_ctor_get(v_cfg_1518_, 4);
v_weakLeancArgs_1525_ = lean_ctor_get(v_cfg_1518_, 5);
v_moreLinkObjs_1526_ = lean_ctor_get(v_cfg_1518_, 6);
v_moreLinkLibs_1527_ = lean_ctor_get(v_cfg_1518_, 7);
v_moreLinkArgs_1528_ = lean_ctor_get(v_cfg_1518_, 8);
v_weakLinkArgs_1529_ = lean_ctor_get(v_cfg_1518_, 9);
v_backend_1530_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13 + 1);
v_platformIndependent_1531_ = lean_ctor_get(v_cfg_1518_, 10);
v_dynlibs_1532_ = lean_ctor_get(v_cfg_1518_, 11);
v_plugins_1533_ = lean_ctor_get(v_cfg_1518_, 12);
v_requiresModuleSystem_1534_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13 + 2);
v_allowNonModules_1535_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13 + 3);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_cfg_1518_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1537_ = v_cfg_1518_;
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_plugins_1533_);
lean_inc(v_dynlibs_1532_);
lean_inc(v_platformIndependent_1531_);
lean_inc(v_weakLinkArgs_1529_);
lean_inc(v_moreLinkArgs_1528_);
lean_inc(v_moreLinkLibs_1527_);
lean_inc(v_moreLinkObjs_1526_);
lean_inc(v_weakLeancArgs_1525_);
lean_inc(v_moreServerOptions_1524_);
lean_inc(v_moreLeancArgs_1523_);
lean_inc(v_weakLeanArgs_1522_);
lean_inc(v_moreLeanArgs_1521_);
lean_inc(v_leanOptions_1520_);
lean_dec(v_cfg_1518_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_apply_1(v_f_1517_, v_weakLeancArgs_1525_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 5, v___x_1539_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v_leanOptions_1520_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_moreLeanArgs_1521_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_weakLeanArgs_1522_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_moreLeancArgs_1523_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_moreServerOptions_1524_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_moreLinkObjs_1526_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_moreLinkLibs_1527_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_moreLinkArgs_1528_);
lean_ctor_set(v_reuseFailAlloc_1542_, 9, v_weakLinkArgs_1529_);
lean_ctor_set(v_reuseFailAlloc_1542_, 10, v_platformIndependent_1531_);
lean_ctor_set(v_reuseFailAlloc_1542_, 11, v_dynlibs_1532_);
lean_ctor_set(v_reuseFailAlloc_1542_, 12, v_plugins_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*13, v_buildType_1519_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*13 + 1, v_backend_1530_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1542_, sizeof(void*)*13 + 3, v_allowNonModules_1535_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1554_){
_start:
{
lean_object* v_moreLinkObjs_1555_; 
v_moreLinkObjs_1555_ = lean_ctor_get(v_cfg_1554_, 6);
lean_inc_ref(v_moreLinkObjs_1555_);
return v_moreLinkObjs_1555_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1556_){
_start:
{
lean_object* v_res_1557_; 
v_res_1557_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1556_);
lean_dec_ref(v_cfg_1556_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1558_, lean_object* v_cfg_1559_){
_start:
{
uint8_t v_buildType_1560_; lean_object* v_leanOptions_1561_; lean_object* v_moreLeanArgs_1562_; lean_object* v_weakLeanArgs_1563_; lean_object* v_moreLeancArgs_1564_; lean_object* v_moreServerOptions_1565_; lean_object* v_weakLeancArgs_1566_; lean_object* v_moreLinkLibs_1567_; lean_object* v_moreLinkArgs_1568_; lean_object* v_weakLinkArgs_1569_; uint8_t v_backend_1570_; lean_object* v_platformIndependent_1571_; lean_object* v_dynlibs_1572_; lean_object* v_plugins_1573_; uint8_t v_requiresModuleSystem_1574_; uint8_t v_allowNonModules_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
v_buildType_1560_ = lean_ctor_get_uint8(v_cfg_1559_, sizeof(void*)*13);
v_leanOptions_1561_ = lean_ctor_get(v_cfg_1559_, 0);
v_moreLeanArgs_1562_ = lean_ctor_get(v_cfg_1559_, 1);
v_weakLeanArgs_1563_ = lean_ctor_get(v_cfg_1559_, 2);
v_moreLeancArgs_1564_ = lean_ctor_get(v_cfg_1559_, 3);
v_moreServerOptions_1565_ = lean_ctor_get(v_cfg_1559_, 4);
v_weakLeancArgs_1566_ = lean_ctor_get(v_cfg_1559_, 5);
v_moreLinkLibs_1567_ = lean_ctor_get(v_cfg_1559_, 7);
v_moreLinkArgs_1568_ = lean_ctor_get(v_cfg_1559_, 8);
v_weakLinkArgs_1569_ = lean_ctor_get(v_cfg_1559_, 9);
v_backend_1570_ = lean_ctor_get_uint8(v_cfg_1559_, sizeof(void*)*13 + 1);
v_platformIndependent_1571_ = lean_ctor_get(v_cfg_1559_, 10);
v_dynlibs_1572_ = lean_ctor_get(v_cfg_1559_, 11);
v_plugins_1573_ = lean_ctor_get(v_cfg_1559_, 12);
v_requiresModuleSystem_1574_ = lean_ctor_get_uint8(v_cfg_1559_, sizeof(void*)*13 + 2);
v_allowNonModules_1575_ = lean_ctor_get_uint8(v_cfg_1559_, sizeof(void*)*13 + 3);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_cfg_1559_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; 
v_unused_1583_ = lean_ctor_get(v_cfg_1559_, 6);
lean_dec(v_unused_1583_);
v___x_1577_ = v_cfg_1559_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_plugins_1573_);
lean_inc(v_dynlibs_1572_);
lean_inc(v_platformIndependent_1571_);
lean_inc(v_weakLinkArgs_1569_);
lean_inc(v_moreLinkArgs_1568_);
lean_inc(v_moreLinkLibs_1567_);
lean_inc(v_weakLeancArgs_1566_);
lean_inc(v_moreServerOptions_1565_);
lean_inc(v_moreLeancArgs_1564_);
lean_inc(v_weakLeanArgs_1563_);
lean_inc(v_moreLeanArgs_1562_);
lean_inc(v_leanOptions_1561_);
lean_dec(v_cfg_1559_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 6, v_val_1558_);
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_leanOptions_1561_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_moreLeanArgs_1562_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_weakLeanArgs_1563_);
lean_ctor_set(v_reuseFailAlloc_1581_, 3, v_moreLeancArgs_1564_);
lean_ctor_set(v_reuseFailAlloc_1581_, 4, v_moreServerOptions_1565_);
lean_ctor_set(v_reuseFailAlloc_1581_, 5, v_weakLeancArgs_1566_);
lean_ctor_set(v_reuseFailAlloc_1581_, 6, v_val_1558_);
lean_ctor_set(v_reuseFailAlloc_1581_, 7, v_moreLinkLibs_1567_);
lean_ctor_set(v_reuseFailAlloc_1581_, 8, v_moreLinkArgs_1568_);
lean_ctor_set(v_reuseFailAlloc_1581_, 9, v_weakLinkArgs_1569_);
lean_ctor_set(v_reuseFailAlloc_1581_, 10, v_platformIndependent_1571_);
lean_ctor_set(v_reuseFailAlloc_1581_, 11, v_dynlibs_1572_);
lean_ctor_set(v_reuseFailAlloc_1581_, 12, v_plugins_1573_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*13, v_buildType_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*13 + 1, v_backend_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1574_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*13 + 3, v_allowNonModules_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1584_, lean_object* v_cfg_1585_){
_start:
{
uint8_t v_buildType_1586_; lean_object* v_leanOptions_1587_; lean_object* v_moreLeanArgs_1588_; lean_object* v_weakLeanArgs_1589_; lean_object* v_moreLeancArgs_1590_; lean_object* v_moreServerOptions_1591_; lean_object* v_weakLeancArgs_1592_; lean_object* v_moreLinkObjs_1593_; lean_object* v_moreLinkLibs_1594_; lean_object* v_moreLinkArgs_1595_; lean_object* v_weakLinkArgs_1596_; uint8_t v_backend_1597_; lean_object* v_platformIndependent_1598_; lean_object* v_dynlibs_1599_; lean_object* v_plugins_1600_; uint8_t v_requiresModuleSystem_1601_; uint8_t v_allowNonModules_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
v_buildType_1586_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*13);
v_leanOptions_1587_ = lean_ctor_get(v_cfg_1585_, 0);
v_moreLeanArgs_1588_ = lean_ctor_get(v_cfg_1585_, 1);
v_weakLeanArgs_1589_ = lean_ctor_get(v_cfg_1585_, 2);
v_moreLeancArgs_1590_ = lean_ctor_get(v_cfg_1585_, 3);
v_moreServerOptions_1591_ = lean_ctor_get(v_cfg_1585_, 4);
v_weakLeancArgs_1592_ = lean_ctor_get(v_cfg_1585_, 5);
v_moreLinkObjs_1593_ = lean_ctor_get(v_cfg_1585_, 6);
v_moreLinkLibs_1594_ = lean_ctor_get(v_cfg_1585_, 7);
v_moreLinkArgs_1595_ = lean_ctor_get(v_cfg_1585_, 8);
v_weakLinkArgs_1596_ = lean_ctor_get(v_cfg_1585_, 9);
v_backend_1597_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*13 + 1);
v_platformIndependent_1598_ = lean_ctor_get(v_cfg_1585_, 10);
v_dynlibs_1599_ = lean_ctor_get(v_cfg_1585_, 11);
v_plugins_1600_ = lean_ctor_get(v_cfg_1585_, 12);
v_requiresModuleSystem_1601_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*13 + 2);
v_allowNonModules_1602_ = lean_ctor_get_uint8(v_cfg_1585_, sizeof(void*)*13 + 3);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_cfg_1585_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v_cfg_1585_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_plugins_1600_);
lean_inc(v_dynlibs_1599_);
lean_inc(v_platformIndependent_1598_);
lean_inc(v_weakLinkArgs_1596_);
lean_inc(v_moreLinkArgs_1595_);
lean_inc(v_moreLinkLibs_1594_);
lean_inc(v_moreLinkObjs_1593_);
lean_inc(v_weakLeancArgs_1592_);
lean_inc(v_moreServerOptions_1591_);
lean_inc(v_moreLeancArgs_1590_);
lean_inc(v_weakLeanArgs_1589_);
lean_inc(v_moreLeanArgs_1588_);
lean_inc(v_leanOptions_1587_);
lean_dec(v_cfg_1585_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = lean_apply_1(v_f_1584_, v_moreLinkObjs_1593_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 6, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_leanOptions_1587_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_moreLeanArgs_1588_);
lean_ctor_set(v_reuseFailAlloc_1609_, 2, v_weakLeanArgs_1589_);
lean_ctor_set(v_reuseFailAlloc_1609_, 3, v_moreLeancArgs_1590_);
lean_ctor_set(v_reuseFailAlloc_1609_, 4, v_moreServerOptions_1591_);
lean_ctor_set(v_reuseFailAlloc_1609_, 5, v_weakLeancArgs_1592_);
lean_ctor_set(v_reuseFailAlloc_1609_, 6, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1609_, 7, v_moreLinkLibs_1594_);
lean_ctor_set(v_reuseFailAlloc_1609_, 8, v_moreLinkArgs_1595_);
lean_ctor_set(v_reuseFailAlloc_1609_, 9, v_weakLinkArgs_1596_);
lean_ctor_set(v_reuseFailAlloc_1609_, 10, v_platformIndependent_1598_);
lean_ctor_set(v_reuseFailAlloc_1609_, 11, v_dynlibs_1599_);
lean_ctor_set(v_reuseFailAlloc_1609_, 12, v_plugins_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*13, v_buildType_1586_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*13 + 1, v_backend_1597_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1609_, sizeof(void*)*13 + 3, v_allowNonModules_1602_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1613_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1615_);
lean_dec_ref(v_x_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1628_){
_start:
{
lean_object* v_moreLinkLibs_1629_; 
v_moreLinkLibs_1629_ = lean_ctor_get(v_cfg_1628_, 7);
lean_inc_ref(v_moreLinkLibs_1629_);
return v_moreLinkLibs_1629_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1630_);
lean_dec_ref(v_cfg_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1632_, lean_object* v_cfg_1633_){
_start:
{
uint8_t v_buildType_1634_; lean_object* v_leanOptions_1635_; lean_object* v_moreLeanArgs_1636_; lean_object* v_weakLeanArgs_1637_; lean_object* v_moreLeancArgs_1638_; lean_object* v_moreServerOptions_1639_; lean_object* v_weakLeancArgs_1640_; lean_object* v_moreLinkObjs_1641_; lean_object* v_moreLinkArgs_1642_; lean_object* v_weakLinkArgs_1643_; uint8_t v_backend_1644_; lean_object* v_platformIndependent_1645_; lean_object* v_dynlibs_1646_; lean_object* v_plugins_1647_; uint8_t v_requiresModuleSystem_1648_; uint8_t v_allowNonModules_1649_; lean_object* v___x_1651_; uint8_t v_isShared_1652_; uint8_t v_isSharedCheck_1656_; 
v_buildType_1634_ = lean_ctor_get_uint8(v_cfg_1633_, sizeof(void*)*13);
v_leanOptions_1635_ = lean_ctor_get(v_cfg_1633_, 0);
v_moreLeanArgs_1636_ = lean_ctor_get(v_cfg_1633_, 1);
v_weakLeanArgs_1637_ = lean_ctor_get(v_cfg_1633_, 2);
v_moreLeancArgs_1638_ = lean_ctor_get(v_cfg_1633_, 3);
v_moreServerOptions_1639_ = lean_ctor_get(v_cfg_1633_, 4);
v_weakLeancArgs_1640_ = lean_ctor_get(v_cfg_1633_, 5);
v_moreLinkObjs_1641_ = lean_ctor_get(v_cfg_1633_, 6);
v_moreLinkArgs_1642_ = lean_ctor_get(v_cfg_1633_, 8);
v_weakLinkArgs_1643_ = lean_ctor_get(v_cfg_1633_, 9);
v_backend_1644_ = lean_ctor_get_uint8(v_cfg_1633_, sizeof(void*)*13 + 1);
v_platformIndependent_1645_ = lean_ctor_get(v_cfg_1633_, 10);
v_dynlibs_1646_ = lean_ctor_get(v_cfg_1633_, 11);
v_plugins_1647_ = lean_ctor_get(v_cfg_1633_, 12);
v_requiresModuleSystem_1648_ = lean_ctor_get_uint8(v_cfg_1633_, sizeof(void*)*13 + 2);
v_allowNonModules_1649_ = lean_ctor_get_uint8(v_cfg_1633_, sizeof(void*)*13 + 3);
v_isSharedCheck_1656_ = !lean_is_exclusive(v_cfg_1633_);
if (v_isSharedCheck_1656_ == 0)
{
lean_object* v_unused_1657_; 
v_unused_1657_ = lean_ctor_get(v_cfg_1633_, 7);
lean_dec(v_unused_1657_);
v___x_1651_ = v_cfg_1633_;
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
else
{
lean_inc(v_plugins_1647_);
lean_inc(v_dynlibs_1646_);
lean_inc(v_platformIndependent_1645_);
lean_inc(v_weakLinkArgs_1643_);
lean_inc(v_moreLinkArgs_1642_);
lean_inc(v_moreLinkObjs_1641_);
lean_inc(v_weakLeancArgs_1640_);
lean_inc(v_moreServerOptions_1639_);
lean_inc(v_moreLeancArgs_1638_);
lean_inc(v_weakLeanArgs_1637_);
lean_inc(v_moreLeanArgs_1636_);
lean_inc(v_leanOptions_1635_);
lean_dec(v_cfg_1633_);
v___x_1651_ = lean_box(0);
v_isShared_1652_ = v_isSharedCheck_1656_;
goto v_resetjp_1650_;
}
v_resetjp_1650_:
{
lean_object* v___x_1654_; 
if (v_isShared_1652_ == 0)
{
lean_ctor_set(v___x_1651_, 7, v_val_1632_);
v___x_1654_ = v___x_1651_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_leanOptions_1635_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_moreLeanArgs_1636_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_weakLeanArgs_1637_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_moreLeancArgs_1638_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_moreServerOptions_1639_);
lean_ctor_set(v_reuseFailAlloc_1655_, 5, v_weakLeancArgs_1640_);
lean_ctor_set(v_reuseFailAlloc_1655_, 6, v_moreLinkObjs_1641_);
lean_ctor_set(v_reuseFailAlloc_1655_, 7, v_val_1632_);
lean_ctor_set(v_reuseFailAlloc_1655_, 8, v_moreLinkArgs_1642_);
lean_ctor_set(v_reuseFailAlloc_1655_, 9, v_weakLinkArgs_1643_);
lean_ctor_set(v_reuseFailAlloc_1655_, 10, v_platformIndependent_1645_);
lean_ctor_set(v_reuseFailAlloc_1655_, 11, v_dynlibs_1646_);
lean_ctor_set(v_reuseFailAlloc_1655_, 12, v_plugins_1647_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*13, v_buildType_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*13 + 1, v_backend_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1655_, sizeof(void*)*13 + 3, v_allowNonModules_1649_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1658_, lean_object* v_cfg_1659_){
_start:
{
uint8_t v_buildType_1660_; lean_object* v_leanOptions_1661_; lean_object* v_moreLeanArgs_1662_; lean_object* v_weakLeanArgs_1663_; lean_object* v_moreLeancArgs_1664_; lean_object* v_moreServerOptions_1665_; lean_object* v_weakLeancArgs_1666_; lean_object* v_moreLinkObjs_1667_; lean_object* v_moreLinkLibs_1668_; lean_object* v_moreLinkArgs_1669_; lean_object* v_weakLinkArgs_1670_; uint8_t v_backend_1671_; lean_object* v_platformIndependent_1672_; lean_object* v_dynlibs_1673_; lean_object* v_plugins_1674_; uint8_t v_requiresModuleSystem_1675_; uint8_t v_allowNonModules_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1684_; 
v_buildType_1660_ = lean_ctor_get_uint8(v_cfg_1659_, sizeof(void*)*13);
v_leanOptions_1661_ = lean_ctor_get(v_cfg_1659_, 0);
v_moreLeanArgs_1662_ = lean_ctor_get(v_cfg_1659_, 1);
v_weakLeanArgs_1663_ = lean_ctor_get(v_cfg_1659_, 2);
v_moreLeancArgs_1664_ = lean_ctor_get(v_cfg_1659_, 3);
v_moreServerOptions_1665_ = lean_ctor_get(v_cfg_1659_, 4);
v_weakLeancArgs_1666_ = lean_ctor_get(v_cfg_1659_, 5);
v_moreLinkObjs_1667_ = lean_ctor_get(v_cfg_1659_, 6);
v_moreLinkLibs_1668_ = lean_ctor_get(v_cfg_1659_, 7);
v_moreLinkArgs_1669_ = lean_ctor_get(v_cfg_1659_, 8);
v_weakLinkArgs_1670_ = lean_ctor_get(v_cfg_1659_, 9);
v_backend_1671_ = lean_ctor_get_uint8(v_cfg_1659_, sizeof(void*)*13 + 1);
v_platformIndependent_1672_ = lean_ctor_get(v_cfg_1659_, 10);
v_dynlibs_1673_ = lean_ctor_get(v_cfg_1659_, 11);
v_plugins_1674_ = lean_ctor_get(v_cfg_1659_, 12);
v_requiresModuleSystem_1675_ = lean_ctor_get_uint8(v_cfg_1659_, sizeof(void*)*13 + 2);
v_allowNonModules_1676_ = lean_ctor_get_uint8(v_cfg_1659_, sizeof(void*)*13 + 3);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_cfg_1659_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1678_ = v_cfg_1659_;
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_plugins_1674_);
lean_inc(v_dynlibs_1673_);
lean_inc(v_platformIndependent_1672_);
lean_inc(v_weakLinkArgs_1670_);
lean_inc(v_moreLinkArgs_1669_);
lean_inc(v_moreLinkLibs_1668_);
lean_inc(v_moreLinkObjs_1667_);
lean_inc(v_weakLeancArgs_1666_);
lean_inc(v_moreServerOptions_1665_);
lean_inc(v_moreLeancArgs_1664_);
lean_inc(v_weakLeanArgs_1663_);
lean_inc(v_moreLeanArgs_1662_);
lean_inc(v_leanOptions_1661_);
lean_dec(v_cfg_1659_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1684_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = lean_apply_1(v_f_1658_, v_moreLinkLibs_1668_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 7, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_leanOptions_1661_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_moreLeanArgs_1662_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_weakLeanArgs_1663_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_moreLeancArgs_1664_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_moreServerOptions_1665_);
lean_ctor_set(v_reuseFailAlloc_1683_, 5, v_weakLeancArgs_1666_);
lean_ctor_set(v_reuseFailAlloc_1683_, 6, v_moreLinkObjs_1667_);
lean_ctor_set(v_reuseFailAlloc_1683_, 7, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1683_, 8, v_moreLinkArgs_1669_);
lean_ctor_set(v_reuseFailAlloc_1683_, 9, v_weakLinkArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1683_, 10, v_platformIndependent_1672_);
lean_ctor_set(v_reuseFailAlloc_1683_, 11, v_dynlibs_1673_);
lean_ctor_set(v_reuseFailAlloc_1683_, 12, v_plugins_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*13, v_buildType_1660_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*13 + 1, v_backend_1671_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1683_, sizeof(void*)*13 + 3, v_allowNonModules_1676_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1695_){
_start:
{
lean_object* v_moreLinkArgs_1696_; 
v_moreLinkArgs_1696_ = lean_ctor_get(v_cfg_1695_, 8);
lean_inc_ref(v_moreLinkArgs_1696_);
return v_moreLinkArgs_1696_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1697_);
lean_dec_ref(v_cfg_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1699_, lean_object* v_cfg_1700_){
_start:
{
uint8_t v_buildType_1701_; lean_object* v_leanOptions_1702_; lean_object* v_moreLeanArgs_1703_; lean_object* v_weakLeanArgs_1704_; lean_object* v_moreLeancArgs_1705_; lean_object* v_moreServerOptions_1706_; lean_object* v_weakLeancArgs_1707_; lean_object* v_moreLinkObjs_1708_; lean_object* v_moreLinkLibs_1709_; lean_object* v_weakLinkArgs_1710_; uint8_t v_backend_1711_; lean_object* v_platformIndependent_1712_; lean_object* v_dynlibs_1713_; lean_object* v_plugins_1714_; uint8_t v_requiresModuleSystem_1715_; uint8_t v_allowNonModules_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
v_buildType_1701_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13);
v_leanOptions_1702_ = lean_ctor_get(v_cfg_1700_, 0);
v_moreLeanArgs_1703_ = lean_ctor_get(v_cfg_1700_, 1);
v_weakLeanArgs_1704_ = lean_ctor_get(v_cfg_1700_, 2);
v_moreLeancArgs_1705_ = lean_ctor_get(v_cfg_1700_, 3);
v_moreServerOptions_1706_ = lean_ctor_get(v_cfg_1700_, 4);
v_weakLeancArgs_1707_ = lean_ctor_get(v_cfg_1700_, 5);
v_moreLinkObjs_1708_ = lean_ctor_get(v_cfg_1700_, 6);
v_moreLinkLibs_1709_ = lean_ctor_get(v_cfg_1700_, 7);
v_weakLinkArgs_1710_ = lean_ctor_get(v_cfg_1700_, 9);
v_backend_1711_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13 + 1);
v_platformIndependent_1712_ = lean_ctor_get(v_cfg_1700_, 10);
v_dynlibs_1713_ = lean_ctor_get(v_cfg_1700_, 11);
v_plugins_1714_ = lean_ctor_get(v_cfg_1700_, 12);
v_requiresModuleSystem_1715_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13 + 2);
v_allowNonModules_1716_ = lean_ctor_get_uint8(v_cfg_1700_, sizeof(void*)*13 + 3);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_cfg_1700_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v_cfg_1700_, 8);
lean_dec(v_unused_1724_);
v___x_1718_ = v_cfg_1700_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_plugins_1714_);
lean_inc(v_dynlibs_1713_);
lean_inc(v_platformIndependent_1712_);
lean_inc(v_weakLinkArgs_1710_);
lean_inc(v_moreLinkLibs_1709_);
lean_inc(v_moreLinkObjs_1708_);
lean_inc(v_weakLeancArgs_1707_);
lean_inc(v_moreServerOptions_1706_);
lean_inc(v_moreLeancArgs_1705_);
lean_inc(v_weakLeanArgs_1704_);
lean_inc(v_moreLeanArgs_1703_);
lean_inc(v_leanOptions_1702_);
lean_dec(v_cfg_1700_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 8, v_val_1699_);
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_leanOptions_1702_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_moreLeanArgs_1703_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_weakLeanArgs_1704_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_moreLeancArgs_1705_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_moreServerOptions_1706_);
lean_ctor_set(v_reuseFailAlloc_1722_, 5, v_weakLeancArgs_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 6, v_moreLinkObjs_1708_);
lean_ctor_set(v_reuseFailAlloc_1722_, 7, v_moreLinkLibs_1709_);
lean_ctor_set(v_reuseFailAlloc_1722_, 8, v_val_1699_);
lean_ctor_set(v_reuseFailAlloc_1722_, 9, v_weakLinkArgs_1710_);
lean_ctor_set(v_reuseFailAlloc_1722_, 10, v_platformIndependent_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 11, v_dynlibs_1713_);
lean_ctor_set(v_reuseFailAlloc_1722_, 12, v_plugins_1714_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13, v_buildType_1701_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13 + 1, v_backend_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1722_, sizeof(void*)*13 + 3, v_allowNonModules_1716_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1725_, lean_object* v_cfg_1726_){
_start:
{
uint8_t v_buildType_1727_; lean_object* v_leanOptions_1728_; lean_object* v_moreLeanArgs_1729_; lean_object* v_weakLeanArgs_1730_; lean_object* v_moreLeancArgs_1731_; lean_object* v_moreServerOptions_1732_; lean_object* v_weakLeancArgs_1733_; lean_object* v_moreLinkObjs_1734_; lean_object* v_moreLinkLibs_1735_; lean_object* v_moreLinkArgs_1736_; lean_object* v_weakLinkArgs_1737_; uint8_t v_backend_1738_; lean_object* v_platformIndependent_1739_; lean_object* v_dynlibs_1740_; lean_object* v_plugins_1741_; uint8_t v_requiresModuleSystem_1742_; uint8_t v_allowNonModules_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
v_buildType_1727_ = lean_ctor_get_uint8(v_cfg_1726_, sizeof(void*)*13);
v_leanOptions_1728_ = lean_ctor_get(v_cfg_1726_, 0);
v_moreLeanArgs_1729_ = lean_ctor_get(v_cfg_1726_, 1);
v_weakLeanArgs_1730_ = lean_ctor_get(v_cfg_1726_, 2);
v_moreLeancArgs_1731_ = lean_ctor_get(v_cfg_1726_, 3);
v_moreServerOptions_1732_ = lean_ctor_get(v_cfg_1726_, 4);
v_weakLeancArgs_1733_ = lean_ctor_get(v_cfg_1726_, 5);
v_moreLinkObjs_1734_ = lean_ctor_get(v_cfg_1726_, 6);
v_moreLinkLibs_1735_ = lean_ctor_get(v_cfg_1726_, 7);
v_moreLinkArgs_1736_ = lean_ctor_get(v_cfg_1726_, 8);
v_weakLinkArgs_1737_ = lean_ctor_get(v_cfg_1726_, 9);
v_backend_1738_ = lean_ctor_get_uint8(v_cfg_1726_, sizeof(void*)*13 + 1);
v_platformIndependent_1739_ = lean_ctor_get(v_cfg_1726_, 10);
v_dynlibs_1740_ = lean_ctor_get(v_cfg_1726_, 11);
v_plugins_1741_ = lean_ctor_get(v_cfg_1726_, 12);
v_requiresModuleSystem_1742_ = lean_ctor_get_uint8(v_cfg_1726_, sizeof(void*)*13 + 2);
v_allowNonModules_1743_ = lean_ctor_get_uint8(v_cfg_1726_, sizeof(void*)*13 + 3);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_cfg_1726_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1745_ = v_cfg_1726_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_plugins_1741_);
lean_inc(v_dynlibs_1740_);
lean_inc(v_platformIndependent_1739_);
lean_inc(v_weakLinkArgs_1737_);
lean_inc(v_moreLinkArgs_1736_);
lean_inc(v_moreLinkLibs_1735_);
lean_inc(v_moreLinkObjs_1734_);
lean_inc(v_weakLeancArgs_1733_);
lean_inc(v_moreServerOptions_1732_);
lean_inc(v_moreLeancArgs_1731_);
lean_inc(v_weakLeanArgs_1730_);
lean_inc(v_moreLeanArgs_1729_);
lean_inc(v_leanOptions_1728_);
lean_dec(v_cfg_1726_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_apply_1(v_f_1725_, v_moreLinkArgs_1736_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 8, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_leanOptions_1728_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_moreLeanArgs_1729_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_weakLeanArgs_1730_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_moreLeancArgs_1731_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_moreServerOptions_1732_);
lean_ctor_set(v_reuseFailAlloc_1750_, 5, v_weakLeancArgs_1733_);
lean_ctor_set(v_reuseFailAlloc_1750_, 6, v_moreLinkObjs_1734_);
lean_ctor_set(v_reuseFailAlloc_1750_, 7, v_moreLinkLibs_1735_);
lean_ctor_set(v_reuseFailAlloc_1750_, 8, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1750_, 9, v_weakLinkArgs_1737_);
lean_ctor_set(v_reuseFailAlloc_1750_, 10, v_platformIndependent_1739_);
lean_ctor_set(v_reuseFailAlloc_1750_, 11, v_dynlibs_1740_);
lean_ctor_set(v_reuseFailAlloc_1750_, 12, v_plugins_1741_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*13, v_buildType_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*13 + 1, v_backend_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*13 + 3, v_allowNonModules_1743_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1762_){
_start:
{
lean_object* v_weakLinkArgs_1763_; 
v_weakLinkArgs_1763_ = lean_ctor_get(v_cfg_1762_, 9);
lean_inc_ref(v_weakLinkArgs_1763_);
return v_weakLinkArgs_1763_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1764_);
lean_dec_ref(v_cfg_1764_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1766_, lean_object* v_cfg_1767_){
_start:
{
uint8_t v_buildType_1768_; lean_object* v_leanOptions_1769_; lean_object* v_moreLeanArgs_1770_; lean_object* v_weakLeanArgs_1771_; lean_object* v_moreLeancArgs_1772_; lean_object* v_moreServerOptions_1773_; lean_object* v_weakLeancArgs_1774_; lean_object* v_moreLinkObjs_1775_; lean_object* v_moreLinkLibs_1776_; lean_object* v_moreLinkArgs_1777_; uint8_t v_backend_1778_; lean_object* v_platformIndependent_1779_; lean_object* v_dynlibs_1780_; lean_object* v_plugins_1781_; uint8_t v_requiresModuleSystem_1782_; uint8_t v_allowNonModules_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_buildType_1768_ = lean_ctor_get_uint8(v_cfg_1767_, sizeof(void*)*13);
v_leanOptions_1769_ = lean_ctor_get(v_cfg_1767_, 0);
v_moreLeanArgs_1770_ = lean_ctor_get(v_cfg_1767_, 1);
v_weakLeanArgs_1771_ = lean_ctor_get(v_cfg_1767_, 2);
v_moreLeancArgs_1772_ = lean_ctor_get(v_cfg_1767_, 3);
v_moreServerOptions_1773_ = lean_ctor_get(v_cfg_1767_, 4);
v_weakLeancArgs_1774_ = lean_ctor_get(v_cfg_1767_, 5);
v_moreLinkObjs_1775_ = lean_ctor_get(v_cfg_1767_, 6);
v_moreLinkLibs_1776_ = lean_ctor_get(v_cfg_1767_, 7);
v_moreLinkArgs_1777_ = lean_ctor_get(v_cfg_1767_, 8);
v_backend_1778_ = lean_ctor_get_uint8(v_cfg_1767_, sizeof(void*)*13 + 1);
v_platformIndependent_1779_ = lean_ctor_get(v_cfg_1767_, 10);
v_dynlibs_1780_ = lean_ctor_get(v_cfg_1767_, 11);
v_plugins_1781_ = lean_ctor_get(v_cfg_1767_, 12);
v_requiresModuleSystem_1782_ = lean_ctor_get_uint8(v_cfg_1767_, sizeof(void*)*13 + 2);
v_allowNonModules_1783_ = lean_ctor_get_uint8(v_cfg_1767_, sizeof(void*)*13 + 3);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_cfg_1767_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_cfg_1767_, 9);
lean_dec(v_unused_1791_);
v___x_1785_ = v_cfg_1767_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_plugins_1781_);
lean_inc(v_dynlibs_1780_);
lean_inc(v_platformIndependent_1779_);
lean_inc(v_moreLinkArgs_1777_);
lean_inc(v_moreLinkLibs_1776_);
lean_inc(v_moreLinkObjs_1775_);
lean_inc(v_weakLeancArgs_1774_);
lean_inc(v_moreServerOptions_1773_);
lean_inc(v_moreLeancArgs_1772_);
lean_inc(v_weakLeanArgs_1771_);
lean_inc(v_moreLeanArgs_1770_);
lean_inc(v_leanOptions_1769_);
lean_dec(v_cfg_1767_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
lean_ctor_set(v___x_1785_, 9, v_val_1766_);
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_leanOptions_1769_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_moreLeanArgs_1770_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_weakLeanArgs_1771_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_moreLeancArgs_1772_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_moreServerOptions_1773_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_weakLeancArgs_1774_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_moreLinkObjs_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_moreLinkLibs_1776_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v_moreLinkArgs_1777_);
lean_ctor_set(v_reuseFailAlloc_1789_, 9, v_val_1766_);
lean_ctor_set(v_reuseFailAlloc_1789_, 10, v_platformIndependent_1779_);
lean_ctor_set(v_reuseFailAlloc_1789_, 11, v_dynlibs_1780_);
lean_ctor_set(v_reuseFailAlloc_1789_, 12, v_plugins_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13, v_buildType_1768_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 1, v_backend_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 3, v_allowNonModules_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1792_, lean_object* v_cfg_1793_){
_start:
{
uint8_t v_buildType_1794_; lean_object* v_leanOptions_1795_; lean_object* v_moreLeanArgs_1796_; lean_object* v_weakLeanArgs_1797_; lean_object* v_moreLeancArgs_1798_; lean_object* v_moreServerOptions_1799_; lean_object* v_weakLeancArgs_1800_; lean_object* v_moreLinkObjs_1801_; lean_object* v_moreLinkLibs_1802_; lean_object* v_moreLinkArgs_1803_; lean_object* v_weakLinkArgs_1804_; uint8_t v_backend_1805_; lean_object* v_platformIndependent_1806_; lean_object* v_dynlibs_1807_; lean_object* v_plugins_1808_; uint8_t v_requiresModuleSystem_1809_; uint8_t v_allowNonModules_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1818_; 
v_buildType_1794_ = lean_ctor_get_uint8(v_cfg_1793_, sizeof(void*)*13);
v_leanOptions_1795_ = lean_ctor_get(v_cfg_1793_, 0);
v_moreLeanArgs_1796_ = lean_ctor_get(v_cfg_1793_, 1);
v_weakLeanArgs_1797_ = lean_ctor_get(v_cfg_1793_, 2);
v_moreLeancArgs_1798_ = lean_ctor_get(v_cfg_1793_, 3);
v_moreServerOptions_1799_ = lean_ctor_get(v_cfg_1793_, 4);
v_weakLeancArgs_1800_ = lean_ctor_get(v_cfg_1793_, 5);
v_moreLinkObjs_1801_ = lean_ctor_get(v_cfg_1793_, 6);
v_moreLinkLibs_1802_ = lean_ctor_get(v_cfg_1793_, 7);
v_moreLinkArgs_1803_ = lean_ctor_get(v_cfg_1793_, 8);
v_weakLinkArgs_1804_ = lean_ctor_get(v_cfg_1793_, 9);
v_backend_1805_ = lean_ctor_get_uint8(v_cfg_1793_, sizeof(void*)*13 + 1);
v_platformIndependent_1806_ = lean_ctor_get(v_cfg_1793_, 10);
v_dynlibs_1807_ = lean_ctor_get(v_cfg_1793_, 11);
v_plugins_1808_ = lean_ctor_get(v_cfg_1793_, 12);
v_requiresModuleSystem_1809_ = lean_ctor_get_uint8(v_cfg_1793_, sizeof(void*)*13 + 2);
v_allowNonModules_1810_ = lean_ctor_get_uint8(v_cfg_1793_, sizeof(void*)*13 + 3);
v_isSharedCheck_1818_ = !lean_is_exclusive(v_cfg_1793_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1812_ = v_cfg_1793_;
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_plugins_1808_);
lean_inc(v_dynlibs_1807_);
lean_inc(v_platformIndependent_1806_);
lean_inc(v_weakLinkArgs_1804_);
lean_inc(v_moreLinkArgs_1803_);
lean_inc(v_moreLinkLibs_1802_);
lean_inc(v_moreLinkObjs_1801_);
lean_inc(v_weakLeancArgs_1800_);
lean_inc(v_moreServerOptions_1799_);
lean_inc(v_moreLeancArgs_1798_);
lean_inc(v_weakLeanArgs_1797_);
lean_inc(v_moreLeanArgs_1796_);
lean_inc(v_leanOptions_1795_);
lean_dec(v_cfg_1793_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1818_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_apply_1(v_f_1792_, v_weakLinkArgs_1804_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 9, v___x_1814_);
v___x_1816_ = v___x_1812_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_leanOptions_1795_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_moreLeanArgs_1796_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_weakLeanArgs_1797_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_moreLeancArgs_1798_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_moreServerOptions_1799_);
lean_ctor_set(v_reuseFailAlloc_1817_, 5, v_weakLeancArgs_1800_);
lean_ctor_set(v_reuseFailAlloc_1817_, 6, v_moreLinkObjs_1801_);
lean_ctor_set(v_reuseFailAlloc_1817_, 7, v_moreLinkLibs_1802_);
lean_ctor_set(v_reuseFailAlloc_1817_, 8, v_moreLinkArgs_1803_);
lean_ctor_set(v_reuseFailAlloc_1817_, 9, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1817_, 10, v_platformIndependent_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 11, v_dynlibs_1807_);
lean_ctor_set(v_reuseFailAlloc_1817_, 12, v_plugins_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*13, v_buildType_1794_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*13 + 1, v_backend_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1817_, sizeof(void*)*13 + 3, v_allowNonModules_1810_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1829_){
_start:
{
uint8_t v_backend_1830_; 
v_backend_1830_ = lean_ctor_get_uint8(v_cfg_1829_, sizeof(void*)*13 + 1);
return v_backend_1830_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1831_){
_start:
{
uint8_t v_res_1832_; lean_object* v_r_1833_; 
v_res_1832_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1831_);
lean_dec_ref(v_cfg_1831_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1834_, lean_object* v_cfg_1835_){
_start:
{
uint8_t v_buildType_1836_; lean_object* v_leanOptions_1837_; lean_object* v_moreLeanArgs_1838_; lean_object* v_weakLeanArgs_1839_; lean_object* v_moreLeancArgs_1840_; lean_object* v_moreServerOptions_1841_; lean_object* v_weakLeancArgs_1842_; lean_object* v_moreLinkObjs_1843_; lean_object* v_moreLinkLibs_1844_; lean_object* v_moreLinkArgs_1845_; lean_object* v_weakLinkArgs_1846_; lean_object* v_platformIndependent_1847_; lean_object* v_dynlibs_1848_; lean_object* v_plugins_1849_; uint8_t v_requiresModuleSystem_1850_; uint8_t v_allowNonModules_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
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
v_platformIndependent_1847_ = lean_ctor_get(v_cfg_1835_, 10);
v_dynlibs_1848_ = lean_ctor_get(v_cfg_1835_, 11);
v_plugins_1849_ = lean_ctor_get(v_cfg_1835_, 12);
v_requiresModuleSystem_1850_ = lean_ctor_get_uint8(v_cfg_1835_, sizeof(void*)*13 + 2);
v_allowNonModules_1851_ = lean_ctor_get_uint8(v_cfg_1835_, sizeof(void*)*13 + 3);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_cfg_1835_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v_cfg_1835_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_plugins_1849_);
lean_inc(v_dynlibs_1848_);
lean_inc(v_platformIndependent_1847_);
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
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_leanOptions_1837_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_moreLeanArgs_1838_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_weakLeanArgs_1839_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_moreLeancArgs_1840_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_moreServerOptions_1841_);
lean_ctor_set(v_reuseFailAlloc_1857_, 5, v_weakLeancArgs_1842_);
lean_ctor_set(v_reuseFailAlloc_1857_, 6, v_moreLinkObjs_1843_);
lean_ctor_set(v_reuseFailAlloc_1857_, 7, v_moreLinkLibs_1844_);
lean_ctor_set(v_reuseFailAlloc_1857_, 8, v_moreLinkArgs_1845_);
lean_ctor_set(v_reuseFailAlloc_1857_, 9, v_weakLinkArgs_1846_);
lean_ctor_set(v_reuseFailAlloc_1857_, 10, v_platformIndependent_1847_);
lean_ctor_set(v_reuseFailAlloc_1857_, 11, v_dynlibs_1848_);
lean_ctor_set(v_reuseFailAlloc_1857_, 12, v_plugins_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*13, v_buildType_1836_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1857_, sizeof(void*)*13 + 3, v_allowNonModules_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_ctor_set_uint8(v___x_1856_, sizeof(void*)*13 + 1, v_val_1834_);
return v___x_1856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1859_, lean_object* v_cfg_1860_){
_start:
{
uint8_t v_val_85__boxed_1861_; lean_object* v_res_1862_; 
v_val_85__boxed_1861_ = lean_unbox(v_val_1859_);
v_res_1862_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_85__boxed_1861_, v_cfg_1860_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1863_, lean_object* v_cfg_1864_){
_start:
{
uint8_t v_buildType_1865_; lean_object* v_leanOptions_1866_; lean_object* v_moreLeanArgs_1867_; lean_object* v_weakLeanArgs_1868_; lean_object* v_moreLeancArgs_1869_; lean_object* v_moreServerOptions_1870_; lean_object* v_weakLeancArgs_1871_; lean_object* v_moreLinkObjs_1872_; lean_object* v_moreLinkLibs_1873_; lean_object* v_moreLinkArgs_1874_; lean_object* v_weakLinkArgs_1875_; uint8_t v_backend_1876_; lean_object* v_platformIndependent_1877_; lean_object* v_dynlibs_1878_; lean_object* v_plugins_1879_; uint8_t v_requiresModuleSystem_1880_; uint8_t v_allowNonModules_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1891_; 
v_buildType_1865_ = lean_ctor_get_uint8(v_cfg_1864_, sizeof(void*)*13);
v_leanOptions_1866_ = lean_ctor_get(v_cfg_1864_, 0);
v_moreLeanArgs_1867_ = lean_ctor_get(v_cfg_1864_, 1);
v_weakLeanArgs_1868_ = lean_ctor_get(v_cfg_1864_, 2);
v_moreLeancArgs_1869_ = lean_ctor_get(v_cfg_1864_, 3);
v_moreServerOptions_1870_ = lean_ctor_get(v_cfg_1864_, 4);
v_weakLeancArgs_1871_ = lean_ctor_get(v_cfg_1864_, 5);
v_moreLinkObjs_1872_ = lean_ctor_get(v_cfg_1864_, 6);
v_moreLinkLibs_1873_ = lean_ctor_get(v_cfg_1864_, 7);
v_moreLinkArgs_1874_ = lean_ctor_get(v_cfg_1864_, 8);
v_weakLinkArgs_1875_ = lean_ctor_get(v_cfg_1864_, 9);
v_backend_1876_ = lean_ctor_get_uint8(v_cfg_1864_, sizeof(void*)*13 + 1);
v_platformIndependent_1877_ = lean_ctor_get(v_cfg_1864_, 10);
v_dynlibs_1878_ = lean_ctor_get(v_cfg_1864_, 11);
v_plugins_1879_ = lean_ctor_get(v_cfg_1864_, 12);
v_requiresModuleSystem_1880_ = lean_ctor_get_uint8(v_cfg_1864_, sizeof(void*)*13 + 2);
v_allowNonModules_1881_ = lean_ctor_get_uint8(v_cfg_1864_, sizeof(void*)*13 + 3);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_cfg_1864_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1883_ = v_cfg_1864_;
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_plugins_1879_);
lean_inc(v_dynlibs_1878_);
lean_inc(v_platformIndependent_1877_);
lean_inc(v_weakLinkArgs_1875_);
lean_inc(v_moreLinkArgs_1874_);
lean_inc(v_moreLinkLibs_1873_);
lean_inc(v_moreLinkObjs_1872_);
lean_inc(v_weakLeancArgs_1871_);
lean_inc(v_moreServerOptions_1870_);
lean_inc(v_moreLeancArgs_1869_);
lean_inc(v_weakLeanArgs_1868_);
lean_inc(v_moreLeanArgs_1867_);
lean_inc(v_leanOptions_1866_);
lean_dec(v_cfg_1864_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1891_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1888_; 
v___x_1885_ = lean_box(v_backend_1876_);
v___x_1886_ = lean_apply_1(v_f_1863_, v___x_1885_);
if (v_isShared_1884_ == 0)
{
v___x_1888_ = v___x_1883_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_leanOptions_1866_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_moreLeanArgs_1867_);
lean_ctor_set(v_reuseFailAlloc_1890_, 2, v_weakLeanArgs_1868_);
lean_ctor_set(v_reuseFailAlloc_1890_, 3, v_moreLeancArgs_1869_);
lean_ctor_set(v_reuseFailAlloc_1890_, 4, v_moreServerOptions_1870_);
lean_ctor_set(v_reuseFailAlloc_1890_, 5, v_weakLeancArgs_1871_);
lean_ctor_set(v_reuseFailAlloc_1890_, 6, v_moreLinkObjs_1872_);
lean_ctor_set(v_reuseFailAlloc_1890_, 7, v_moreLinkLibs_1873_);
lean_ctor_set(v_reuseFailAlloc_1890_, 8, v_moreLinkArgs_1874_);
lean_ctor_set(v_reuseFailAlloc_1890_, 9, v_weakLinkArgs_1875_);
lean_ctor_set(v_reuseFailAlloc_1890_, 10, v_platformIndependent_1877_);
lean_ctor_set(v_reuseFailAlloc_1890_, 11, v_dynlibs_1878_);
lean_ctor_set(v_reuseFailAlloc_1890_, 12, v_plugins_1879_);
lean_ctor_set_uint8(v_reuseFailAlloc_1890_, sizeof(void*)*13, v_buildType_1865_);
v___x_1888_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_unbox(v___x_1886_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*13 + 1, v___x_1889_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1880_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*13 + 3, v_allowNonModules_1881_);
return v___x_1888_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1892_){
_start:
{
uint8_t v___x_1893_; 
v___x_1893_ = 2;
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1894_){
_start:
{
uint8_t v_res_1895_; lean_object* v_r_1896_; 
v_res_1895_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1894_);
lean_dec_ref(v_x_1894_);
v_r_1896_ = lean_box(v_res_1895_);
return v_r_1896_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1908_){
_start:
{
lean_object* v_platformIndependent_1909_; 
v_platformIndependent_1909_ = lean_ctor_get(v_cfg_1908_, 10);
lean_inc(v_platformIndependent_1909_);
return v_platformIndependent_1909_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1910_);
lean_dec_ref(v_cfg_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1912_, lean_object* v_cfg_1913_){
_start:
{
uint8_t v_buildType_1914_; lean_object* v_leanOptions_1915_; lean_object* v_moreLeanArgs_1916_; lean_object* v_weakLeanArgs_1917_; lean_object* v_moreLeancArgs_1918_; lean_object* v_moreServerOptions_1919_; lean_object* v_weakLeancArgs_1920_; lean_object* v_moreLinkObjs_1921_; lean_object* v_moreLinkLibs_1922_; lean_object* v_moreLinkArgs_1923_; lean_object* v_weakLinkArgs_1924_; uint8_t v_backend_1925_; lean_object* v_dynlibs_1926_; lean_object* v_plugins_1927_; uint8_t v_requiresModuleSystem_1928_; uint8_t v_allowNonModules_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_buildType_1914_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*13);
v_leanOptions_1915_ = lean_ctor_get(v_cfg_1913_, 0);
v_moreLeanArgs_1916_ = lean_ctor_get(v_cfg_1913_, 1);
v_weakLeanArgs_1917_ = lean_ctor_get(v_cfg_1913_, 2);
v_moreLeancArgs_1918_ = lean_ctor_get(v_cfg_1913_, 3);
v_moreServerOptions_1919_ = lean_ctor_get(v_cfg_1913_, 4);
v_weakLeancArgs_1920_ = lean_ctor_get(v_cfg_1913_, 5);
v_moreLinkObjs_1921_ = lean_ctor_get(v_cfg_1913_, 6);
v_moreLinkLibs_1922_ = lean_ctor_get(v_cfg_1913_, 7);
v_moreLinkArgs_1923_ = lean_ctor_get(v_cfg_1913_, 8);
v_weakLinkArgs_1924_ = lean_ctor_get(v_cfg_1913_, 9);
v_backend_1925_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*13 + 1);
v_dynlibs_1926_ = lean_ctor_get(v_cfg_1913_, 11);
v_plugins_1927_ = lean_ctor_get(v_cfg_1913_, 12);
v_requiresModuleSystem_1928_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*13 + 2);
v_allowNonModules_1929_ = lean_ctor_get_uint8(v_cfg_1913_, sizeof(void*)*13 + 3);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_cfg_1913_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_cfg_1913_, 10);
lean_dec(v_unused_1937_);
v___x_1931_ = v_cfg_1913_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_plugins_1927_);
lean_inc(v_dynlibs_1926_);
lean_inc(v_weakLinkArgs_1924_);
lean_inc(v_moreLinkArgs_1923_);
lean_inc(v_moreLinkLibs_1922_);
lean_inc(v_moreLinkObjs_1921_);
lean_inc(v_weakLeancArgs_1920_);
lean_inc(v_moreServerOptions_1919_);
lean_inc(v_moreLeancArgs_1918_);
lean_inc(v_weakLeanArgs_1917_);
lean_inc(v_moreLeanArgs_1916_);
lean_inc(v_leanOptions_1915_);
lean_dec(v_cfg_1913_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 10, v_val_1912_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_leanOptions_1915_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_moreLeanArgs_1916_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_weakLeanArgs_1917_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_moreLeancArgs_1918_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_moreServerOptions_1919_);
lean_ctor_set(v_reuseFailAlloc_1935_, 5, v_weakLeancArgs_1920_);
lean_ctor_set(v_reuseFailAlloc_1935_, 6, v_moreLinkObjs_1921_);
lean_ctor_set(v_reuseFailAlloc_1935_, 7, v_moreLinkLibs_1922_);
lean_ctor_set(v_reuseFailAlloc_1935_, 8, v_moreLinkArgs_1923_);
lean_ctor_set(v_reuseFailAlloc_1935_, 9, v_weakLinkArgs_1924_);
lean_ctor_set(v_reuseFailAlloc_1935_, 10, v_val_1912_);
lean_ctor_set(v_reuseFailAlloc_1935_, 11, v_dynlibs_1926_);
lean_ctor_set(v_reuseFailAlloc_1935_, 12, v_plugins_1927_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*13, v_buildType_1914_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*13 + 1, v_backend_1925_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*13 + 3, v_allowNonModules_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_1938_, lean_object* v_cfg_1939_){
_start:
{
uint8_t v_buildType_1940_; lean_object* v_leanOptions_1941_; lean_object* v_moreLeanArgs_1942_; lean_object* v_weakLeanArgs_1943_; lean_object* v_moreLeancArgs_1944_; lean_object* v_moreServerOptions_1945_; lean_object* v_weakLeancArgs_1946_; lean_object* v_moreLinkObjs_1947_; lean_object* v_moreLinkLibs_1948_; lean_object* v_moreLinkArgs_1949_; lean_object* v_weakLinkArgs_1950_; uint8_t v_backend_1951_; lean_object* v_platformIndependent_1952_; lean_object* v_dynlibs_1953_; lean_object* v_plugins_1954_; uint8_t v_requiresModuleSystem_1955_; uint8_t v_allowNonModules_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1964_; 
v_buildType_1940_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*13);
v_leanOptions_1941_ = lean_ctor_get(v_cfg_1939_, 0);
v_moreLeanArgs_1942_ = lean_ctor_get(v_cfg_1939_, 1);
v_weakLeanArgs_1943_ = lean_ctor_get(v_cfg_1939_, 2);
v_moreLeancArgs_1944_ = lean_ctor_get(v_cfg_1939_, 3);
v_moreServerOptions_1945_ = lean_ctor_get(v_cfg_1939_, 4);
v_weakLeancArgs_1946_ = lean_ctor_get(v_cfg_1939_, 5);
v_moreLinkObjs_1947_ = lean_ctor_get(v_cfg_1939_, 6);
v_moreLinkLibs_1948_ = lean_ctor_get(v_cfg_1939_, 7);
v_moreLinkArgs_1949_ = lean_ctor_get(v_cfg_1939_, 8);
v_weakLinkArgs_1950_ = lean_ctor_get(v_cfg_1939_, 9);
v_backend_1951_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*13 + 1);
v_platformIndependent_1952_ = lean_ctor_get(v_cfg_1939_, 10);
v_dynlibs_1953_ = lean_ctor_get(v_cfg_1939_, 11);
v_plugins_1954_ = lean_ctor_get(v_cfg_1939_, 12);
v_requiresModuleSystem_1955_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*13 + 2);
v_allowNonModules_1956_ = lean_ctor_get_uint8(v_cfg_1939_, sizeof(void*)*13 + 3);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_cfg_1939_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1958_ = v_cfg_1939_;
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_plugins_1954_);
lean_inc(v_dynlibs_1953_);
lean_inc(v_platformIndependent_1952_);
lean_inc(v_weakLinkArgs_1950_);
lean_inc(v_moreLinkArgs_1949_);
lean_inc(v_moreLinkLibs_1948_);
lean_inc(v_moreLinkObjs_1947_);
lean_inc(v_weakLeancArgs_1946_);
lean_inc(v_moreServerOptions_1945_);
lean_inc(v_moreLeancArgs_1944_);
lean_inc(v_weakLeanArgs_1943_);
lean_inc(v_moreLeanArgs_1942_);
lean_inc(v_leanOptions_1941_);
lean_dec(v_cfg_1939_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = lean_apply_1(v_f_1938_, v_platformIndependent_1952_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 10, v___x_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_leanOptions_1941_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_moreLeanArgs_1942_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_weakLeanArgs_1943_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_moreLeancArgs_1944_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v_moreServerOptions_1945_);
lean_ctor_set(v_reuseFailAlloc_1963_, 5, v_weakLeancArgs_1946_);
lean_ctor_set(v_reuseFailAlloc_1963_, 6, v_moreLinkObjs_1947_);
lean_ctor_set(v_reuseFailAlloc_1963_, 7, v_moreLinkLibs_1948_);
lean_ctor_set(v_reuseFailAlloc_1963_, 8, v_moreLinkArgs_1949_);
lean_ctor_set(v_reuseFailAlloc_1963_, 9, v_weakLinkArgs_1950_);
lean_ctor_set(v_reuseFailAlloc_1963_, 10, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1963_, 11, v_dynlibs_1953_);
lean_ctor_set(v_reuseFailAlloc_1963_, 12, v_plugins_1954_);
lean_ctor_set_uint8(v_reuseFailAlloc_1963_, sizeof(void*)*13, v_buildType_1940_);
lean_ctor_set_uint8(v_reuseFailAlloc_1963_, sizeof(void*)*13 + 1, v_backend_1951_);
lean_ctor_set_uint8(v_reuseFailAlloc_1963_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1963_, sizeof(void*)*13 + 3, v_allowNonModules_1956_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_1965_){
_start:
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_box(0);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_1967_);
lean_dec_ref(v_x_1967_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_1980_){
_start:
{
lean_object* v_dynlibs_1981_; 
v_dynlibs_1981_ = lean_ctor_get(v_cfg_1980_, 11);
lean_inc_ref(v_dynlibs_1981_);
return v_dynlibs_1981_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_1982_);
lean_dec_ref(v_cfg_1982_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_1984_, lean_object* v_cfg_1985_){
_start:
{
uint8_t v_buildType_1986_; lean_object* v_leanOptions_1987_; lean_object* v_moreLeanArgs_1988_; lean_object* v_weakLeanArgs_1989_; lean_object* v_moreLeancArgs_1990_; lean_object* v_moreServerOptions_1991_; lean_object* v_weakLeancArgs_1992_; lean_object* v_moreLinkObjs_1993_; lean_object* v_moreLinkLibs_1994_; lean_object* v_moreLinkArgs_1995_; lean_object* v_weakLinkArgs_1996_; uint8_t v_backend_1997_; lean_object* v_platformIndependent_1998_; lean_object* v_plugins_1999_; uint8_t v_requiresModuleSystem_2000_; uint8_t v_allowNonModules_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
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
v_plugins_1999_ = lean_ctor_get(v_cfg_1985_, 12);
v_requiresModuleSystem_2000_ = lean_ctor_get_uint8(v_cfg_1985_, sizeof(void*)*13 + 2);
v_allowNonModules_2001_ = lean_ctor_get_uint8(v_cfg_1985_, sizeof(void*)*13 + 3);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_cfg_1985_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v_cfg_1985_, 11);
lean_dec(v_unused_2009_);
v___x_2003_ = v_cfg_1985_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_plugins_1999_);
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
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 11, v_val_1984_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_leanOptions_1987_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_moreLeanArgs_1988_);
lean_ctor_set(v_reuseFailAlloc_2007_, 2, v_weakLeanArgs_1989_);
lean_ctor_set(v_reuseFailAlloc_2007_, 3, v_moreLeancArgs_1990_);
lean_ctor_set(v_reuseFailAlloc_2007_, 4, v_moreServerOptions_1991_);
lean_ctor_set(v_reuseFailAlloc_2007_, 5, v_weakLeancArgs_1992_);
lean_ctor_set(v_reuseFailAlloc_2007_, 6, v_moreLinkObjs_1993_);
lean_ctor_set(v_reuseFailAlloc_2007_, 7, v_moreLinkLibs_1994_);
lean_ctor_set(v_reuseFailAlloc_2007_, 8, v_moreLinkArgs_1995_);
lean_ctor_set(v_reuseFailAlloc_2007_, 9, v_weakLinkArgs_1996_);
lean_ctor_set(v_reuseFailAlloc_2007_, 10, v_platformIndependent_1998_);
lean_ctor_set(v_reuseFailAlloc_2007_, 11, v_val_1984_);
lean_ctor_set(v_reuseFailAlloc_2007_, 12, v_plugins_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2007_, sizeof(void*)*13, v_buildType_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2007_, sizeof(void*)*13 + 1, v_backend_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2007_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2007_, sizeof(void*)*13 + 3, v_allowNonModules_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_2010_, lean_object* v_cfg_2011_){
_start:
{
uint8_t v_buildType_2012_; lean_object* v_leanOptions_2013_; lean_object* v_moreLeanArgs_2014_; lean_object* v_weakLeanArgs_2015_; lean_object* v_moreLeancArgs_2016_; lean_object* v_moreServerOptions_2017_; lean_object* v_weakLeancArgs_2018_; lean_object* v_moreLinkObjs_2019_; lean_object* v_moreLinkLibs_2020_; lean_object* v_moreLinkArgs_2021_; lean_object* v_weakLinkArgs_2022_; uint8_t v_backend_2023_; lean_object* v_platformIndependent_2024_; lean_object* v_dynlibs_2025_; lean_object* v_plugins_2026_; uint8_t v_requiresModuleSystem_2027_; uint8_t v_allowNonModules_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2036_; 
v_buildType_2012_ = lean_ctor_get_uint8(v_cfg_2011_, sizeof(void*)*13);
v_leanOptions_2013_ = lean_ctor_get(v_cfg_2011_, 0);
v_moreLeanArgs_2014_ = lean_ctor_get(v_cfg_2011_, 1);
v_weakLeanArgs_2015_ = lean_ctor_get(v_cfg_2011_, 2);
v_moreLeancArgs_2016_ = lean_ctor_get(v_cfg_2011_, 3);
v_moreServerOptions_2017_ = lean_ctor_get(v_cfg_2011_, 4);
v_weakLeancArgs_2018_ = lean_ctor_get(v_cfg_2011_, 5);
v_moreLinkObjs_2019_ = lean_ctor_get(v_cfg_2011_, 6);
v_moreLinkLibs_2020_ = lean_ctor_get(v_cfg_2011_, 7);
v_moreLinkArgs_2021_ = lean_ctor_get(v_cfg_2011_, 8);
v_weakLinkArgs_2022_ = lean_ctor_get(v_cfg_2011_, 9);
v_backend_2023_ = lean_ctor_get_uint8(v_cfg_2011_, sizeof(void*)*13 + 1);
v_platformIndependent_2024_ = lean_ctor_get(v_cfg_2011_, 10);
v_dynlibs_2025_ = lean_ctor_get(v_cfg_2011_, 11);
v_plugins_2026_ = lean_ctor_get(v_cfg_2011_, 12);
v_requiresModuleSystem_2027_ = lean_ctor_get_uint8(v_cfg_2011_, sizeof(void*)*13 + 2);
v_allowNonModules_2028_ = lean_ctor_get_uint8(v_cfg_2011_, sizeof(void*)*13 + 3);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_cfg_2011_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2030_ = v_cfg_2011_;
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_plugins_2026_);
lean_inc(v_dynlibs_2025_);
lean_inc(v_platformIndependent_2024_);
lean_inc(v_weakLinkArgs_2022_);
lean_inc(v_moreLinkArgs_2021_);
lean_inc(v_moreLinkLibs_2020_);
lean_inc(v_moreLinkObjs_2019_);
lean_inc(v_weakLeancArgs_2018_);
lean_inc(v_moreServerOptions_2017_);
lean_inc(v_moreLeancArgs_2016_);
lean_inc(v_weakLeanArgs_2015_);
lean_inc(v_moreLeanArgs_2014_);
lean_inc(v_leanOptions_2013_);
lean_dec(v_cfg_2011_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2032_ = lean_apply_1(v_f_2010_, v_dynlibs_2025_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 11, v___x_2032_);
v___x_2034_ = v___x_2030_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_leanOptions_2013_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_moreLeanArgs_2014_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_weakLeanArgs_2015_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_moreLeancArgs_2016_);
lean_ctor_set(v_reuseFailAlloc_2035_, 4, v_moreServerOptions_2017_);
lean_ctor_set(v_reuseFailAlloc_2035_, 5, v_weakLeancArgs_2018_);
lean_ctor_set(v_reuseFailAlloc_2035_, 6, v_moreLinkObjs_2019_);
lean_ctor_set(v_reuseFailAlloc_2035_, 7, v_moreLinkLibs_2020_);
lean_ctor_set(v_reuseFailAlloc_2035_, 8, v_moreLinkArgs_2021_);
lean_ctor_set(v_reuseFailAlloc_2035_, 9, v_weakLinkArgs_2022_);
lean_ctor_set(v_reuseFailAlloc_2035_, 10, v_platformIndependent_2024_);
lean_ctor_set(v_reuseFailAlloc_2035_, 11, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2035_, 12, v_plugins_2026_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*13, v_buildType_2012_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*13 + 1, v_backend_2023_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2035_, sizeof(void*)*13 + 3, v_allowNonModules_2028_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_2047_){
_start:
{
lean_object* v_plugins_2048_; 
v_plugins_2048_ = lean_ctor_get(v_cfg_2047_, 12);
lean_inc_ref(v_plugins_2048_);
return v_plugins_2048_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_2049_);
lean_dec_ref(v_cfg_2049_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_2051_, lean_object* v_cfg_2052_){
_start:
{
uint8_t v_buildType_2053_; lean_object* v_leanOptions_2054_; lean_object* v_moreLeanArgs_2055_; lean_object* v_weakLeanArgs_2056_; lean_object* v_moreLeancArgs_2057_; lean_object* v_moreServerOptions_2058_; lean_object* v_weakLeancArgs_2059_; lean_object* v_moreLinkObjs_2060_; lean_object* v_moreLinkLibs_2061_; lean_object* v_moreLinkArgs_2062_; lean_object* v_weakLinkArgs_2063_; uint8_t v_backend_2064_; lean_object* v_platformIndependent_2065_; lean_object* v_dynlibs_2066_; uint8_t v_requiresModuleSystem_2067_; uint8_t v_allowNonModules_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_buildType_2053_ = lean_ctor_get_uint8(v_cfg_2052_, sizeof(void*)*13);
v_leanOptions_2054_ = lean_ctor_get(v_cfg_2052_, 0);
v_moreLeanArgs_2055_ = lean_ctor_get(v_cfg_2052_, 1);
v_weakLeanArgs_2056_ = lean_ctor_get(v_cfg_2052_, 2);
v_moreLeancArgs_2057_ = lean_ctor_get(v_cfg_2052_, 3);
v_moreServerOptions_2058_ = lean_ctor_get(v_cfg_2052_, 4);
v_weakLeancArgs_2059_ = lean_ctor_get(v_cfg_2052_, 5);
v_moreLinkObjs_2060_ = lean_ctor_get(v_cfg_2052_, 6);
v_moreLinkLibs_2061_ = lean_ctor_get(v_cfg_2052_, 7);
v_moreLinkArgs_2062_ = lean_ctor_get(v_cfg_2052_, 8);
v_weakLinkArgs_2063_ = lean_ctor_get(v_cfg_2052_, 9);
v_backend_2064_ = lean_ctor_get_uint8(v_cfg_2052_, sizeof(void*)*13 + 1);
v_platformIndependent_2065_ = lean_ctor_get(v_cfg_2052_, 10);
v_dynlibs_2066_ = lean_ctor_get(v_cfg_2052_, 11);
v_requiresModuleSystem_2067_ = lean_ctor_get_uint8(v_cfg_2052_, sizeof(void*)*13 + 2);
v_allowNonModules_2068_ = lean_ctor_get_uint8(v_cfg_2052_, sizeof(void*)*13 + 3);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_cfg_2052_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_cfg_2052_, 12);
lean_dec(v_unused_2076_);
v___x_2070_ = v_cfg_2052_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_dynlibs_2066_);
lean_inc(v_platformIndependent_2065_);
lean_inc(v_weakLinkArgs_2063_);
lean_inc(v_moreLinkArgs_2062_);
lean_inc(v_moreLinkLibs_2061_);
lean_inc(v_moreLinkObjs_2060_);
lean_inc(v_weakLeancArgs_2059_);
lean_inc(v_moreServerOptions_2058_);
lean_inc(v_moreLeancArgs_2057_);
lean_inc(v_weakLeanArgs_2056_);
lean_inc(v_moreLeanArgs_2055_);
lean_inc(v_leanOptions_2054_);
lean_dec(v_cfg_2052_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 12, v_val_2051_);
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_leanOptions_2054_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_moreLeanArgs_2055_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_weakLeanArgs_2056_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_moreLeancArgs_2057_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_moreServerOptions_2058_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v_weakLeancArgs_2059_);
lean_ctor_set(v_reuseFailAlloc_2074_, 6, v_moreLinkObjs_2060_);
lean_ctor_set(v_reuseFailAlloc_2074_, 7, v_moreLinkLibs_2061_);
lean_ctor_set(v_reuseFailAlloc_2074_, 8, v_moreLinkArgs_2062_);
lean_ctor_set(v_reuseFailAlloc_2074_, 9, v_weakLinkArgs_2063_);
lean_ctor_set(v_reuseFailAlloc_2074_, 10, v_platformIndependent_2065_);
lean_ctor_set(v_reuseFailAlloc_2074_, 11, v_dynlibs_2066_);
lean_ctor_set(v_reuseFailAlloc_2074_, 12, v_val_2051_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*13, v_buildType_2053_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*13 + 1, v_backend_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2067_);
lean_ctor_set_uint8(v_reuseFailAlloc_2074_, sizeof(void*)*13 + 3, v_allowNonModules_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_2077_, lean_object* v_cfg_2078_){
_start:
{
uint8_t v_buildType_2079_; lean_object* v_leanOptions_2080_; lean_object* v_moreLeanArgs_2081_; lean_object* v_weakLeanArgs_2082_; lean_object* v_moreLeancArgs_2083_; lean_object* v_moreServerOptions_2084_; lean_object* v_weakLeancArgs_2085_; lean_object* v_moreLinkObjs_2086_; lean_object* v_moreLinkLibs_2087_; lean_object* v_moreLinkArgs_2088_; lean_object* v_weakLinkArgs_2089_; uint8_t v_backend_2090_; lean_object* v_platformIndependent_2091_; lean_object* v_dynlibs_2092_; lean_object* v_plugins_2093_; uint8_t v_requiresModuleSystem_2094_; uint8_t v_allowNonModules_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2103_; 
v_buildType_2079_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*13);
v_leanOptions_2080_ = lean_ctor_get(v_cfg_2078_, 0);
v_moreLeanArgs_2081_ = lean_ctor_get(v_cfg_2078_, 1);
v_weakLeanArgs_2082_ = lean_ctor_get(v_cfg_2078_, 2);
v_moreLeancArgs_2083_ = lean_ctor_get(v_cfg_2078_, 3);
v_moreServerOptions_2084_ = lean_ctor_get(v_cfg_2078_, 4);
v_weakLeancArgs_2085_ = lean_ctor_get(v_cfg_2078_, 5);
v_moreLinkObjs_2086_ = lean_ctor_get(v_cfg_2078_, 6);
v_moreLinkLibs_2087_ = lean_ctor_get(v_cfg_2078_, 7);
v_moreLinkArgs_2088_ = lean_ctor_get(v_cfg_2078_, 8);
v_weakLinkArgs_2089_ = lean_ctor_get(v_cfg_2078_, 9);
v_backend_2090_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*13 + 1);
v_platformIndependent_2091_ = lean_ctor_get(v_cfg_2078_, 10);
v_dynlibs_2092_ = lean_ctor_get(v_cfg_2078_, 11);
v_plugins_2093_ = lean_ctor_get(v_cfg_2078_, 12);
v_requiresModuleSystem_2094_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*13 + 2);
v_allowNonModules_2095_ = lean_ctor_get_uint8(v_cfg_2078_, sizeof(void*)*13 + 3);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_cfg_2078_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2097_ = v_cfg_2078_;
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_plugins_2093_);
lean_inc(v_dynlibs_2092_);
lean_inc(v_platformIndependent_2091_);
lean_inc(v_weakLinkArgs_2089_);
lean_inc(v_moreLinkArgs_2088_);
lean_inc(v_moreLinkLibs_2087_);
lean_inc(v_moreLinkObjs_2086_);
lean_inc(v_weakLeancArgs_2085_);
lean_inc(v_moreServerOptions_2084_);
lean_inc(v_moreLeancArgs_2083_);
lean_inc(v_weakLeanArgs_2082_);
lean_inc(v_moreLeanArgs_2081_);
lean_inc(v_leanOptions_2080_);
lean_dec(v_cfg_2078_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2103_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2099_ = lean_apply_1(v_f_2077_, v_plugins_2093_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 12, v___x_2099_);
v___x_2101_ = v___x_2097_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_leanOptions_2080_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_moreLeanArgs_2081_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_weakLeanArgs_2082_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_moreLeancArgs_2083_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_moreServerOptions_2084_);
lean_ctor_set(v_reuseFailAlloc_2102_, 5, v_weakLeancArgs_2085_);
lean_ctor_set(v_reuseFailAlloc_2102_, 6, v_moreLinkObjs_2086_);
lean_ctor_set(v_reuseFailAlloc_2102_, 7, v_moreLinkLibs_2087_);
lean_ctor_set(v_reuseFailAlloc_2102_, 8, v_moreLinkArgs_2088_);
lean_ctor_set(v_reuseFailAlloc_2102_, 9, v_weakLinkArgs_2089_);
lean_ctor_set(v_reuseFailAlloc_2102_, 10, v_platformIndependent_2091_);
lean_ctor_set(v_reuseFailAlloc_2102_, 11, v_dynlibs_2092_);
lean_ctor_set(v_reuseFailAlloc_2102_, 12, v___x_2099_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13, v_buildType_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 1, v_backend_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2102_, sizeof(void*)*13 + 3, v_allowNonModules_2095_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object* v_cfg_2114_){
_start:
{
uint8_t v_requiresModuleSystem_2115_; 
v_requiresModuleSystem_2115_ = lean_ctor_get_uint8(v_cfg_2114_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_2115_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object* v_cfg_2116_){
_start:
{
uint8_t v_res_2117_; lean_object* v_r_2118_; 
v_res_2117_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2116_);
lean_dec_ref(v_cfg_2116_);
v_r_2118_ = lean_box(v_res_2117_);
return v_r_2118_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t v_val_2119_, lean_object* v_cfg_2120_){
_start:
{
uint8_t v_buildType_2121_; lean_object* v_leanOptions_2122_; lean_object* v_moreLeanArgs_2123_; lean_object* v_weakLeanArgs_2124_; lean_object* v_moreLeancArgs_2125_; lean_object* v_moreServerOptions_2126_; lean_object* v_weakLeancArgs_2127_; lean_object* v_moreLinkObjs_2128_; lean_object* v_moreLinkLibs_2129_; lean_object* v_moreLinkArgs_2130_; lean_object* v_weakLinkArgs_2131_; uint8_t v_backend_2132_; lean_object* v_platformIndependent_2133_; lean_object* v_dynlibs_2134_; lean_object* v_plugins_2135_; uint8_t v_allowNonModules_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
v_buildType_2121_ = lean_ctor_get_uint8(v_cfg_2120_, sizeof(void*)*13);
v_leanOptions_2122_ = lean_ctor_get(v_cfg_2120_, 0);
v_moreLeanArgs_2123_ = lean_ctor_get(v_cfg_2120_, 1);
v_weakLeanArgs_2124_ = lean_ctor_get(v_cfg_2120_, 2);
v_moreLeancArgs_2125_ = lean_ctor_get(v_cfg_2120_, 3);
v_moreServerOptions_2126_ = lean_ctor_get(v_cfg_2120_, 4);
v_weakLeancArgs_2127_ = lean_ctor_get(v_cfg_2120_, 5);
v_moreLinkObjs_2128_ = lean_ctor_get(v_cfg_2120_, 6);
v_moreLinkLibs_2129_ = lean_ctor_get(v_cfg_2120_, 7);
v_moreLinkArgs_2130_ = lean_ctor_get(v_cfg_2120_, 8);
v_weakLinkArgs_2131_ = lean_ctor_get(v_cfg_2120_, 9);
v_backend_2132_ = lean_ctor_get_uint8(v_cfg_2120_, sizeof(void*)*13 + 1);
v_platformIndependent_2133_ = lean_ctor_get(v_cfg_2120_, 10);
v_dynlibs_2134_ = lean_ctor_get(v_cfg_2120_, 11);
v_plugins_2135_ = lean_ctor_get(v_cfg_2120_, 12);
v_allowNonModules_2136_ = lean_ctor_get_uint8(v_cfg_2120_, sizeof(void*)*13 + 3);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_cfg_2120_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v_cfg_2120_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_plugins_2135_);
lean_inc(v_dynlibs_2134_);
lean_inc(v_platformIndependent_2133_);
lean_inc(v_weakLinkArgs_2131_);
lean_inc(v_moreLinkArgs_2130_);
lean_inc(v_moreLinkLibs_2129_);
lean_inc(v_moreLinkObjs_2128_);
lean_inc(v_weakLeancArgs_2127_);
lean_inc(v_moreServerOptions_2126_);
lean_inc(v_moreLeancArgs_2125_);
lean_inc(v_weakLeanArgs_2124_);
lean_inc(v_moreLeanArgs_2123_);
lean_inc(v_leanOptions_2122_);
lean_dec(v_cfg_2120_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_leanOptions_2122_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_moreLeanArgs_2123_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_weakLeanArgs_2124_);
lean_ctor_set(v_reuseFailAlloc_2142_, 3, v_moreLeancArgs_2125_);
lean_ctor_set(v_reuseFailAlloc_2142_, 4, v_moreServerOptions_2126_);
lean_ctor_set(v_reuseFailAlloc_2142_, 5, v_weakLeancArgs_2127_);
lean_ctor_set(v_reuseFailAlloc_2142_, 6, v_moreLinkObjs_2128_);
lean_ctor_set(v_reuseFailAlloc_2142_, 7, v_moreLinkLibs_2129_);
lean_ctor_set(v_reuseFailAlloc_2142_, 8, v_moreLinkArgs_2130_);
lean_ctor_set(v_reuseFailAlloc_2142_, 9, v_weakLinkArgs_2131_);
lean_ctor_set(v_reuseFailAlloc_2142_, 10, v_platformIndependent_2133_);
lean_ctor_set(v_reuseFailAlloc_2142_, 11, v_dynlibs_2134_);
lean_ctor_set(v_reuseFailAlloc_2142_, 12, v_plugins_2135_);
lean_ctor_set_uint8(v_reuseFailAlloc_2142_, sizeof(void*)*13, v_buildType_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2142_, sizeof(void*)*13 + 1, v_backend_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2142_, sizeof(void*)*13 + 3, v_allowNonModules_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
lean_ctor_set_uint8(v___x_2141_, sizeof(void*)*13 + 2, v_val_2119_);
return v___x_2141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object* v_val_2144_, lean_object* v_cfg_2145_){
_start:
{
uint8_t v_val_85__boxed_2146_; lean_object* v_res_2147_; 
v_val_85__boxed_2146_ = lean_unbox(v_val_2144_);
v_res_2147_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_85__boxed_2146_, v_cfg_2145_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object* v_f_2148_, lean_object* v_cfg_2149_){
_start:
{
uint8_t v_buildType_2150_; lean_object* v_leanOptions_2151_; lean_object* v_moreLeanArgs_2152_; lean_object* v_weakLeanArgs_2153_; lean_object* v_moreLeancArgs_2154_; lean_object* v_moreServerOptions_2155_; lean_object* v_weakLeancArgs_2156_; lean_object* v_moreLinkObjs_2157_; lean_object* v_moreLinkLibs_2158_; lean_object* v_moreLinkArgs_2159_; lean_object* v_weakLinkArgs_2160_; uint8_t v_backend_2161_; lean_object* v_platformIndependent_2162_; lean_object* v_dynlibs_2163_; lean_object* v_plugins_2164_; uint8_t v_requiresModuleSystem_2165_; uint8_t v_allowNonModules_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2176_; 
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
v_dynlibs_2163_ = lean_ctor_get(v_cfg_2149_, 11);
v_plugins_2164_ = lean_ctor_get(v_cfg_2149_, 12);
v_requiresModuleSystem_2165_ = lean_ctor_get_uint8(v_cfg_2149_, sizeof(void*)*13 + 2);
v_allowNonModules_2166_ = lean_ctor_get_uint8(v_cfg_2149_, sizeof(void*)*13 + 3);
v_isSharedCheck_2176_ = !lean_is_exclusive(v_cfg_2149_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2168_ = v_cfg_2149_;
v_isShared_2169_ = v_isSharedCheck_2176_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_plugins_2164_);
lean_inc(v_dynlibs_2163_);
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
v_isShared_2169_ = v_isSharedCheck_2176_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2170_ = lean_box(v_requiresModuleSystem_2165_);
v___x_2171_ = lean_apply_1(v_f_2148_, v___x_2170_);
if (v_isShared_2169_ == 0)
{
v___x_2173_ = v___x_2168_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_leanOptions_2151_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_moreLeanArgs_2152_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_weakLeanArgs_2153_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_moreLeancArgs_2154_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_moreServerOptions_2155_);
lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_weakLeancArgs_2156_);
lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_moreLinkObjs_2157_);
lean_ctor_set(v_reuseFailAlloc_2175_, 7, v_moreLinkLibs_2158_);
lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_moreLinkArgs_2159_);
lean_ctor_set(v_reuseFailAlloc_2175_, 9, v_weakLinkArgs_2160_);
lean_ctor_set(v_reuseFailAlloc_2175_, 10, v_platformIndependent_2162_);
lean_ctor_set(v_reuseFailAlloc_2175_, 11, v_dynlibs_2163_);
lean_ctor_set(v_reuseFailAlloc_2175_, 12, v_plugins_2164_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*13, v_buildType_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2175_, sizeof(void*)*13 + 1, v_backend_2161_);
v___x_2173_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_unbox(v___x_2171_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*13 + 2, v___x_2174_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*13 + 3, v_allowNonModules_2166_);
return v___x_2173_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3(lean_object* v_x_2177_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = 0;
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3___boxed(lean_object* v_x_2179_){
_start:
{
uint8_t v_res_2180_; lean_object* v_r_2181_; 
v_res_2180_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3(v_x_2179_);
lean_dec_ref(v_x_2179_);
v_r_2181_ = lean_box(v_res_2180_);
return v_r_2181_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object* v_cfg_2193_){
_start:
{
uint8_t v_allowNonModules_2194_; 
v_allowNonModules_2194_ = lean_ctor_get_uint8(v_cfg_2193_, sizeof(void*)*13 + 3);
return v_allowNonModules_2194_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object* v_cfg_2195_){
_start:
{
uint8_t v_res_2196_; lean_object* v_r_2197_; 
v_res_2196_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2195_);
lean_dec_ref(v_cfg_2195_);
v_r_2197_ = lean_box(v_res_2196_);
return v_r_2197_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t v_val_2198_, lean_object* v_cfg_2199_){
_start:
{
uint8_t v_buildType_2200_; lean_object* v_leanOptions_2201_; lean_object* v_moreLeanArgs_2202_; lean_object* v_weakLeanArgs_2203_; lean_object* v_moreLeancArgs_2204_; lean_object* v_moreServerOptions_2205_; lean_object* v_weakLeancArgs_2206_; lean_object* v_moreLinkObjs_2207_; lean_object* v_moreLinkLibs_2208_; lean_object* v_moreLinkArgs_2209_; lean_object* v_weakLinkArgs_2210_; uint8_t v_backend_2211_; lean_object* v_platformIndependent_2212_; lean_object* v_dynlibs_2213_; lean_object* v_plugins_2214_; uint8_t v_requiresModuleSystem_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
v_buildType_2200_ = lean_ctor_get_uint8(v_cfg_2199_, sizeof(void*)*13);
v_leanOptions_2201_ = lean_ctor_get(v_cfg_2199_, 0);
v_moreLeanArgs_2202_ = lean_ctor_get(v_cfg_2199_, 1);
v_weakLeanArgs_2203_ = lean_ctor_get(v_cfg_2199_, 2);
v_moreLeancArgs_2204_ = lean_ctor_get(v_cfg_2199_, 3);
v_moreServerOptions_2205_ = lean_ctor_get(v_cfg_2199_, 4);
v_weakLeancArgs_2206_ = lean_ctor_get(v_cfg_2199_, 5);
v_moreLinkObjs_2207_ = lean_ctor_get(v_cfg_2199_, 6);
v_moreLinkLibs_2208_ = lean_ctor_get(v_cfg_2199_, 7);
v_moreLinkArgs_2209_ = lean_ctor_get(v_cfg_2199_, 8);
v_weakLinkArgs_2210_ = lean_ctor_get(v_cfg_2199_, 9);
v_backend_2211_ = lean_ctor_get_uint8(v_cfg_2199_, sizeof(void*)*13 + 1);
v_platformIndependent_2212_ = lean_ctor_get(v_cfg_2199_, 10);
v_dynlibs_2213_ = lean_ctor_get(v_cfg_2199_, 11);
v_plugins_2214_ = lean_ctor_get(v_cfg_2199_, 12);
v_requiresModuleSystem_2215_ = lean_ctor_get_uint8(v_cfg_2199_, sizeof(void*)*13 + 2);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_cfg_2199_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v_cfg_2199_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_plugins_2214_);
lean_inc(v_dynlibs_2213_);
lean_inc(v_platformIndependent_2212_);
lean_inc(v_weakLinkArgs_2210_);
lean_inc(v_moreLinkArgs_2209_);
lean_inc(v_moreLinkLibs_2208_);
lean_inc(v_moreLinkObjs_2207_);
lean_inc(v_weakLeancArgs_2206_);
lean_inc(v_moreServerOptions_2205_);
lean_inc(v_moreLeancArgs_2204_);
lean_inc(v_weakLeanArgs_2203_);
lean_inc(v_moreLeanArgs_2202_);
lean_inc(v_leanOptions_2201_);
lean_dec(v_cfg_2199_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_leanOptions_2201_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_moreLeanArgs_2202_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_weakLeanArgs_2203_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_moreLeancArgs_2204_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_moreServerOptions_2205_);
lean_ctor_set(v_reuseFailAlloc_2221_, 5, v_weakLeancArgs_2206_);
lean_ctor_set(v_reuseFailAlloc_2221_, 6, v_moreLinkObjs_2207_);
lean_ctor_set(v_reuseFailAlloc_2221_, 7, v_moreLinkLibs_2208_);
lean_ctor_set(v_reuseFailAlloc_2221_, 8, v_moreLinkArgs_2209_);
lean_ctor_set(v_reuseFailAlloc_2221_, 9, v_weakLinkArgs_2210_);
lean_ctor_set(v_reuseFailAlloc_2221_, 10, v_platformIndependent_2212_);
lean_ctor_set(v_reuseFailAlloc_2221_, 11, v_dynlibs_2213_);
lean_ctor_set(v_reuseFailAlloc_2221_, 12, v_plugins_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*13, v_buildType_2200_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*13 + 1, v_backend_2211_);
lean_ctor_set_uint8(v_reuseFailAlloc_2221_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_ctor_set_uint8(v___x_2220_, sizeof(void*)*13 + 3, v_val_2198_);
return v___x_2220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object* v_val_2223_, lean_object* v_cfg_2224_){
_start:
{
uint8_t v_val_85__boxed_2225_; lean_object* v_res_2226_; 
v_val_85__boxed_2225_ = lean_unbox(v_val_2223_);
v_res_2226_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_85__boxed_2225_, v_cfg_2224_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object* v_f_2227_, lean_object* v_cfg_2228_){
_start:
{
uint8_t v_buildType_2229_; lean_object* v_leanOptions_2230_; lean_object* v_moreLeanArgs_2231_; lean_object* v_weakLeanArgs_2232_; lean_object* v_moreLeancArgs_2233_; lean_object* v_moreServerOptions_2234_; lean_object* v_weakLeancArgs_2235_; lean_object* v_moreLinkObjs_2236_; lean_object* v_moreLinkLibs_2237_; lean_object* v_moreLinkArgs_2238_; lean_object* v_weakLinkArgs_2239_; uint8_t v_backend_2240_; lean_object* v_platformIndependent_2241_; lean_object* v_dynlibs_2242_; lean_object* v_plugins_2243_; uint8_t v_requiresModuleSystem_2244_; uint8_t v_allowNonModules_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2255_; 
v_buildType_2229_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*13);
v_leanOptions_2230_ = lean_ctor_get(v_cfg_2228_, 0);
v_moreLeanArgs_2231_ = lean_ctor_get(v_cfg_2228_, 1);
v_weakLeanArgs_2232_ = lean_ctor_get(v_cfg_2228_, 2);
v_moreLeancArgs_2233_ = lean_ctor_get(v_cfg_2228_, 3);
v_moreServerOptions_2234_ = lean_ctor_get(v_cfg_2228_, 4);
v_weakLeancArgs_2235_ = lean_ctor_get(v_cfg_2228_, 5);
v_moreLinkObjs_2236_ = lean_ctor_get(v_cfg_2228_, 6);
v_moreLinkLibs_2237_ = lean_ctor_get(v_cfg_2228_, 7);
v_moreLinkArgs_2238_ = lean_ctor_get(v_cfg_2228_, 8);
v_weakLinkArgs_2239_ = lean_ctor_get(v_cfg_2228_, 9);
v_backend_2240_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*13 + 1);
v_platformIndependent_2241_ = lean_ctor_get(v_cfg_2228_, 10);
v_dynlibs_2242_ = lean_ctor_get(v_cfg_2228_, 11);
v_plugins_2243_ = lean_ctor_get(v_cfg_2228_, 12);
v_requiresModuleSystem_2244_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*13 + 2);
v_allowNonModules_2245_ = lean_ctor_get_uint8(v_cfg_2228_, sizeof(void*)*13 + 3);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_cfg_2228_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2247_ = v_cfg_2228_;
v_isShared_2248_ = v_isSharedCheck_2255_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_plugins_2243_);
lean_inc(v_dynlibs_2242_);
lean_inc(v_platformIndependent_2241_);
lean_inc(v_weakLinkArgs_2239_);
lean_inc(v_moreLinkArgs_2238_);
lean_inc(v_moreLinkLibs_2237_);
lean_inc(v_moreLinkObjs_2236_);
lean_inc(v_weakLeancArgs_2235_);
lean_inc(v_moreServerOptions_2234_);
lean_inc(v_moreLeancArgs_2233_);
lean_inc(v_weakLeanArgs_2232_);
lean_inc(v_moreLeanArgs_2231_);
lean_inc(v_leanOptions_2230_);
lean_dec(v_cfg_2228_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2255_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2249_ = lean_box(v_allowNonModules_2245_);
v___x_2250_ = lean_apply_1(v_f_2227_, v___x_2249_);
if (v_isShared_2248_ == 0)
{
v___x_2252_ = v___x_2247_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_leanOptions_2230_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_moreLeanArgs_2231_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_weakLeanArgs_2232_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_moreLeancArgs_2233_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v_moreServerOptions_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 5, v_weakLeancArgs_2235_);
lean_ctor_set(v_reuseFailAlloc_2254_, 6, v_moreLinkObjs_2236_);
lean_ctor_set(v_reuseFailAlloc_2254_, 7, v_moreLinkLibs_2237_);
lean_ctor_set(v_reuseFailAlloc_2254_, 8, v_moreLinkArgs_2238_);
lean_ctor_set(v_reuseFailAlloc_2254_, 9, v_weakLinkArgs_2239_);
lean_ctor_set(v_reuseFailAlloc_2254_, 10, v_platformIndependent_2241_);
lean_ctor_set(v_reuseFailAlloc_2254_, 11, v_dynlibs_2242_);
lean_ctor_set(v_reuseFailAlloc_2254_, 12, v_plugins_2243_);
lean_ctor_set_uint8(v_reuseFailAlloc_2254_, sizeof(void*)*13, v_buildType_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2254_, sizeof(void*)*13 + 1, v_backend_2240_);
lean_ctor_set_uint8(v_reuseFailAlloc_2254_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2244_);
v___x_2252_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
uint8_t v___x_2253_; 
v___x_2253_ = lean_unbox(v___x_2250_);
lean_ctor_set_uint8(v___x_2252_, sizeof(void*)*13 + 3, v___x_2253_);
return v___x_2252_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2275_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2276_ = lean_array_push(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2284_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2285_ = lean_array_push(v___x_2284_, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2292_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2293_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2294_ = lean_array_push(v___x_2293_, v___x_2292_);
return v___x_2294_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2301_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2302_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2303_ = lean_array_push(v___x_2302_, v___x_2301_);
return v___x_2303_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2310_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2311_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2312_ = lean_array_push(v___x_2311_, v___x_2310_);
return v___x_2312_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2320_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2321_ = lean_array_push(v___x_2320_, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2329_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2330_ = lean_array_push(v___x_2329_, v___x_2328_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2338_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2339_ = lean_array_push(v___x_2338_, v___x_2337_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2346_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2347_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2348_ = lean_array_push(v___x_2347_, v___x_2346_);
return v___x_2348_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2355_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2356_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2357_ = lean_array_push(v___x_2356_, v___x_2355_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2365_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2366_ = lean_array_push(v___x_2365_, v___x_2364_);
return v___x_2366_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2374_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2375_ = lean_array_push(v___x_2374_, v___x_2373_);
return v___x_2375_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2382_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2383_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2384_ = lean_array_push(v___x_2383_, v___x_2382_);
return v___x_2384_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2392_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2393_ = lean_array_push(v___x_2392_, v___x_2391_);
return v___x_2393_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2401_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2402_ = lean_array_push(v___x_2401_, v___x_2400_);
return v___x_2402_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__47));
v___x_2410_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
v___x_2411_ = lean_array_push(v___x_2410_, v___x_2409_);
return v___x_2411_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__51(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__50));
v___x_2419_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__48, &l_Lake_LeanConfig___fields___closed__48_once, _init_l_Lake_LeanConfig___fields___closed__48);
v___x_2420_ = lean_array_push(v___x_2419_, v___x_2418_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__51, &l_Lake_LeanConfig___fields___closed__51_once, _init_l_Lake_LeanConfig___fields___closed__51);
return v___x_2421_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lake_LeanConfig___fields;
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2423_, lean_object* v_x2_2424_){
_start:
{
lean_object* v_name_2425_; lean_object* v___x_2426_; 
v_name_2425_ = lean_ctor_get(v_x2_2424_, 0);
lean_inc(v_name_2425_);
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2425_, v_x2_2424_, v_x1_2423_);
return v___x_2426_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = l_Lake_LeanConfig___fields;
v___x_2428_ = lean_array_get_size(v___x_2427_);
return v___x_2428_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2449_ = lean_unsigned_to_nat(0u);
v___x_2450_ = lean_nat_dec_lt(v___x_2449_, v___x_2448_);
return v___x_2450_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2451_ = lean_unsigned_to_nat(0u);
v___x_2452_ = lean_box(1);
v___x_2453_ = l_Lake_LeanConfig___fields;
v___x_2454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2453_);
lean_ctor_set(v___x_2454_, 1, v___x_2452_);
lean_ctor_set(v___x_2454_, 2, v___x_2451_);
return v___x_2454_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2456_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2457_ = lean_nat_dec_le(v___x_2456_, v___x_2456_);
return v___x_2457_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2458_; size_t v___x_2459_; 
v___x_2458_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2459_ = lean_usize_of_nat(v___x_2458_);
return v___x_2459_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2460_; size_t v___x_2461_; size_t v___x_2462_; lean_object* v___x_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2460_ = lean_box(1);
v___x_2461_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2462_ = ((size_t)0ULL);
v___x_2463_ = l_Lake_LeanConfig___fields;
v___f_2464_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2465_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2466_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2465_, v___f_2464_, v___x_2463_, v___x_2462_, v___x_2461_, v___x_2460_);
return v___x_2466_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2467_ = lean_unsigned_to_nat(0u);
v___x_2468_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2469_ = l_Lake_LeanConfig___fields;
v___x_2470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
lean_ctor_set(v___x_2470_, 1, v___x_2468_);
lean_ctor_set(v___x_2470_, 2, v___x_2467_);
return v___x_2470_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2471_; 
v___x_2471_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
v___x_2472_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2472_;
}
else
{
uint8_t v___x_2473_; 
v___x_2473_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2473_ == 0)
{
if (v___x_2471_ == 0)
{
lean_object* v___x_2474_; 
v___x_2474_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2474_;
}
else
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2475_;
}
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2476_;
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

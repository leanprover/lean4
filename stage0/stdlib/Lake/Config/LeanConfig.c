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
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
uint8_t v_x_171__boxed_112_; lean_object* v_res_113_; 
v_x_171__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Lake_instReprBackend_repr(v_x_171__boxed_112_, v_prec_111_);
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
uint8_t v_x_20__boxed_134_; uint8_t v_y_21__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v_x_20__boxed_134_ = lean_unbox(v_x_132_);
v_y_21__boxed_135_ = lean_unbox(v_y_133_);
v_res_136_ = l_Lake_instDecidableEqBackend(v_x_20__boxed_134_, v_y_21__boxed_135_);
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
uint8_t v_x_12__boxed_177_; uint8_t v_x_13__boxed_178_; uint8_t v_res_179_; lean_object* v_r_180_; 
v_x_12__boxed_177_ = lean_unbox(v_x_175_);
v_x_13__boxed_178_ = lean_unbox(v_x_176_);
v_res_179_ = l_Lake_Backend_orPreferLeft(v_x_12__boxed_177_, v_x_13__boxed_178_);
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
uint8_t v_x_221__boxed_318_; lean_object* v_res_319_; 
v_x_221__boxed_318_ = lean_unbox(v_x_316_);
v_res_319_ = l_Lake_instReprBuildType_repr(v_x_221__boxed_318_, v_prec_317_);
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
uint8_t v_x_20__boxed_343_; uint8_t v_y_21__boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_x_20__boxed_343_ = lean_unbox(v_x_341_);
v_y_21__boxed_344_ = lean_unbox(v_y_342_);
v_res_345_ = l_Lake_instDecidableEqBuildType(v_x_20__boxed_343_, v_y_21__boxed_344_);
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
lean_object* v___y_445_; lean_object* v___x_459_; uint32_t v___x_460_; uint8_t v___y_462_; uint32_t v___x_467_; uint8_t v___x_468_; 
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_string_utf8_get(v_s_443_, v___x_459_);
v___x_467_ = 65;
v___x_468_ = lean_uint32_dec_le(v___x_467_, v___x_460_);
if (v___x_468_ == 0)
{
v___y_462_ = v___x_468_;
goto v___jp_461_;
}
else
{
uint32_t v___x_469_; uint8_t v___x_470_; 
v___x_469_ = 90;
v___x_470_ = lean_uint32_dec_le(v___x_460_, v___x_469_);
v___y_462_ = v___x_470_;
goto v___jp_461_;
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
v___jp_461_:
{
if (v___y_462_ == 0)
{
lean_object* v___x_463_; 
v___x_463_ = lean_string_utf8_set(v_s_443_, v___x_459_, v___x_460_);
v___y_445_ = v___x_463_;
goto v___jp_444_;
}
else
{
uint32_t v___x_464_; uint32_t v___x_465_; lean_object* v___x_466_; 
v___x_464_ = 32;
v___x_465_ = lean_uint32_add(v___x_460_, v___x_464_);
v___x_466_ = lean_string_utf8_set(v_s_443_, v___x_459_, v___x_465_);
v___y_445_ = v___x_466_;
goto v___jp_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString(uint8_t v_bt_471_){
_start:
{
switch(v_bt_471_)
{
case 0:
{
lean_object* v___x_472_; 
v___x_472_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
return v___x_472_;
}
case 1:
{
lean_object* v___x_473_; 
v___x_473_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
return v___x_473_;
}
case 2:
{
lean_object* v___x_474_; 
v___x_474_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
return v___x_474_;
}
default: 
{
lean_object* v___x_475_; 
v___x_475_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString___boxed(lean_object* v_bt_476_){
_start:
{
uint8_t v_bt_boxed_477_; lean_object* v_res_478_; 
v_bt_boxed_477_ = lean_unbox(v_bt_476_);
v_res_478_ = l_Lake_BuildType_toString(v_bt_boxed_477_);
return v_res_478_;
}
}
static lean_object* _init_l_Lake_BuildType_leanOptions___closed__3(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_box(1);
v___x_487_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__2));
v___x_488_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__1));
v___x_489_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_488_, v___x_487_, v___x_486_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions(uint8_t v_x_490_){
_start:
{
if (v_x_490_ == 0)
{
lean_object* v___x_491_; 
v___x_491_ = lean_obj_once(&l_Lake_BuildType_leanOptions___closed__3, &l_Lake_BuildType_leanOptions___closed__3_once, _init_l_Lake_BuildType_leanOptions___closed__3);
return v___x_491_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = lean_box(1);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions___boxed(lean_object* v_x_493_){
_start:
{
uint8_t v_x_66__boxed_494_; lean_object* v_res_495_; 
v_x_66__boxed_494_ = lean_unbox(v_x_493_);
v_res_495_ = l_Lake_BuildType_leanOptions(v_x_66__boxed_494_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs(uint8_t v_t_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___boxed(lean_object* v_t_500_){
_start:
{
uint8_t v_t_boxed_501_; lean_object* v_res_502_; 
v_t_boxed_501_ = lean_unbox(v_t_500_);
v_res_502_ = l_Lake_BuildType_leanArgs(v_t_boxed_501_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v___x_521_; 
v___x_521_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1));
return v___x_521_;
}
else
{
lean_object* v_val_522_; lean_object* v___x_523_; uint8_t v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v_val_522_ = lean_ctor_get(v_x_519_, 0);
v___x_523_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3));
v___x_524_ = lean_unbox(v_val_522_);
v___x_525_ = l_Bool_repr___redArg(v___x_524_);
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_523_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Repr_addAppParen(v___x_526_, v_x_520_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_528_, v_x_529_);
lean_dec(v_x_529_);
lean_dec(v_x_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object* v_a_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_nat_to_int(v_a_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object* v___y_533_){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = l_String_quote(v___y_533_);
v___x_535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_dec(v_x_536_);
return v_x_537_;
}
else
{
lean_object* v_head_539_; lean_object* v_tail_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_551_; 
v_head_539_ = lean_ctor_get(v_x_538_, 0);
v_tail_540_ = lean_ctor_get(v_x_538_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_551_ == 0)
{
v___x_542_ = v_x_538_;
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_tail_540_);
lean_inc(v_head_539_);
lean_dec(v_x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_551_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
lean_inc(v_x_536_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 5);
lean_ctor_set(v___x_542_, 1, v_x_536_);
lean_ctor_set(v___x_542_, 0, v_x_537_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_x_537_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_x_536_);
v___x_545_ = v_reuseFailAlloc_550_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = l_String_quote(v_head_539_);
v___x_547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___x_548_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_545_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v_x_537_ = v___x_548_;
v_x_538_ = v_tail_540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object* v_x_552_, lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_dec(v_x_552_);
return v_x_553_;
}
else
{
lean_object* v_head_555_; lean_object* v_tail_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_567_; 
v_head_555_ = lean_ctor_get(v_x_554_, 0);
v_tail_556_ = lean_ctor_get(v_x_554_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_567_ == 0)
{
v___x_558_ = v_x_554_;
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_tail_556_);
lean_inc(v_head_555_);
lean_dec(v_x_554_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_567_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
lean_inc(v_x_552_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 5);
lean_ctor_set(v___x_558_, 1, v_x_552_);
lean_ctor_set(v___x_558_, 0, v_x_553_);
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_x_553_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_x_552_);
v___x_561_ = v_reuseFailAlloc_566_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_562_ = l_String_quote(v_head_555_);
v___x_563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
v___x_564_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_561_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_552_, v___x_564_, v_tail_556_);
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_568_) == 0)
{
lean_object* v___x_570_; 
lean_dec(v_x_569_);
v___x_570_ = lean_box(0);
return v___x_570_;
}
else
{
lean_object* v_tail_571_; 
v_tail_571_ = lean_ctor_get(v_x_568_, 1);
if (lean_obj_tag(v_tail_571_) == 0)
{
lean_object* v_head_572_; lean_object* v___x_573_; 
lean_dec(v_x_569_);
v_head_572_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_head_572_);
lean_dec_ref_known(v_x_568_, 2);
v___x_573_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_572_);
return v___x_573_;
}
else
{
lean_object* v_head_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_inc(v_tail_571_);
v_head_574_ = lean_ctor_get(v_x_568_, 0);
lean_inc(v_head_574_);
lean_dec_ref_known(v_x_568_, 2);
v___x_575_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_574_);
v___x_576_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_569_, v___x_575_, v_tail_571_);
return v___x_576_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0));
v___x_586_ = lean_string_length(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5);
v___x_588_ = lean_nat_to_int(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object* v_xs_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_597_ = lean_array_get_size(v_xs_596_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_nat_dec_eq(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_600_ = lean_array_to_list(v_xs_596_);
v___x_601_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_602_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_600_, v___x_601_);
v___x_603_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_604_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_605_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
lean_ctor_set(v___x_605_, 1, v___x_602_);
v___x_606_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_603_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = l_Std_Format_fill(v___x_608_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; 
lean_dec_ref(v_xs_596_);
v___x_610_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object* v___y_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = l_Lake_Target_repr___redArg(v___y_611_, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_x_616_){
_start:
{
if (lean_obj_tag(v_x_616_) == 0)
{
lean_dec(v_x_614_);
return v_x_615_;
}
else
{
lean_object* v_head_617_; lean_object* v_tail_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_629_; 
v_head_617_ = lean_ctor_get(v_x_616_, 0);
v_tail_618_ = lean_ctor_get(v_x_616_, 1);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_616_);
if (v_isSharedCheck_629_ == 0)
{
v___x_620_ = v_x_616_;
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_tail_618_);
lean_inc(v_head_617_);
lean_dec(v_x_616_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_629_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_623_; 
lean_inc(v_x_614_);
if (v_isShared_621_ == 0)
{
lean_ctor_set_tag(v___x_620_, 5);
lean_ctor_set(v___x_620_, 1, v_x_614_);
lean_ctor_set(v___x_620_, 0, v_x_615_);
v___x_623_ = v___x_620_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_x_615_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_x_614_);
v___x_623_ = v_reuseFailAlloc_628_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = l_Lake_Target_repr___redArg(v_head_617_, v___x_624_);
v___x_626_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_623_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v_x_615_ = v___x_626_;
v_x_616_ = v_tail_618_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
lean_dec(v_x_630_);
return v_x_631_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_645_; 
v_head_633_ = lean_ctor_get(v_x_632_, 0);
v_tail_634_ = lean_ctor_get(v_x_632_, 1);
v_isSharedCheck_645_ = !lean_is_exclusive(v_x_632_);
if (v_isSharedCheck_645_ == 0)
{
v___x_636_ = v_x_632_;
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_tail_634_);
lean_inc(v_head_633_);
lean_dec(v_x_632_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_645_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
lean_inc(v_x_630_);
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 5);
lean_ctor_set(v___x_636_, 1, v_x_630_);
lean_ctor_set(v___x_636_, 0, v_x_631_);
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_x_631_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_x_630_);
v___x_639_ = v_reuseFailAlloc_644_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = l_Lake_Target_repr___redArg(v_head_633_, v___x_640_);
v___x_642_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_639_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_630_, v___x_642_, v_tail_634_);
return v___x_643_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object* v_x_646_, lean_object* v_x_647_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v___x_648_; 
lean_dec(v_x_647_);
v___x_648_ = lean_box(0);
return v___x_648_;
}
else
{
lean_object* v_tail_649_; 
v_tail_649_ = lean_ctor_get(v_x_646_, 1);
if (lean_obj_tag(v_tail_649_) == 0)
{
lean_object* v_head_650_; lean_object* v___x_651_; 
lean_dec(v_x_647_);
v_head_650_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_head_650_);
lean_dec_ref_known(v_x_646_, 2);
v___x_651_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_650_);
return v___x_651_;
}
else
{
lean_object* v_head_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_inc(v_tail_649_);
v_head_652_ = lean_ctor_get(v_x_646_, 0);
lean_inc(v_head_652_);
lean_dec_ref_known(v_x_646_, 2);
v___x_653_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_652_);
v___x_654_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_647_, v___x_653_, v_tail_649_);
return v___x_654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object* v_xs_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_array_get_size(v_xs_655_);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_nat_dec_eq(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_659_ = lean_array_to_list(v_xs_655_);
v___x_660_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_661_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_659_, v___x_660_);
v___x_662_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_663_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_664_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_661_);
v___x_665_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_666_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_662_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Std_Format_fill(v___x_667_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
lean_dec_ref(v_xs_655_);
v___x_669_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_670_, lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
if (lean_obj_tag(v_x_672_) == 0)
{
lean_dec(v_x_670_);
return v_x_671_;
}
else
{
lean_object* v_head_673_; lean_object* v_tail_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_684_; 
v_head_673_ = lean_ctor_get(v_x_672_, 0);
v_tail_674_ = lean_ctor_get(v_x_672_, 1);
v_isSharedCheck_684_ = !lean_is_exclusive(v_x_672_);
if (v_isSharedCheck_684_ == 0)
{
v___x_676_ = v_x_672_;
v_isShared_677_ = v_isSharedCheck_684_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_tail_674_);
lean_inc(v_head_673_);
lean_dec(v_x_672_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_684_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
lean_inc(v_x_670_);
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 5);
lean_ctor_set(v___x_676_, 1, v_x_670_);
lean_ctor_set(v___x_676_, 0, v_x_671_);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_x_671_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_x_670_);
v___x_679_ = v_reuseFailAlloc_683_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = l_Lean_instReprLeanOption_repr___redArg(v_head_673_);
v___x_681_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_679_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
v_x_671_ = v___x_681_;
v_x_672_ = v_tail_674_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_x_687_){
_start:
{
if (lean_obj_tag(v_x_687_) == 0)
{
lean_dec(v_x_685_);
return v_x_686_;
}
else
{
lean_object* v_head_688_; lean_object* v_tail_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_699_; 
v_head_688_ = lean_ctor_get(v_x_687_, 0);
v_tail_689_ = lean_ctor_get(v_x_687_, 1);
v_isSharedCheck_699_ = !lean_is_exclusive(v_x_687_);
if (v_isSharedCheck_699_ == 0)
{
v___x_691_ = v_x_687_;
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_tail_689_);
lean_inc(v_head_688_);
lean_dec(v_x_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_699_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
lean_inc(v_x_685_);
if (v_isShared_692_ == 0)
{
lean_ctor_set_tag(v___x_691_, 5);
lean_ctor_set(v___x_691_, 1, v_x_685_);
lean_ctor_set(v___x_691_, 0, v_x_686_);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_x_686_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_x_685_);
v___x_694_ = v_reuseFailAlloc_698_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = l_Lean_instReprLeanOption_repr___redArg(v_head_688_);
v___x_696_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_685_, v___x_696_, v_tail_689_);
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object* v_x_700_, lean_object* v_x_701_){
_start:
{
if (lean_obj_tag(v_x_700_) == 0)
{
lean_object* v___x_702_; 
lean_dec(v_x_701_);
v___x_702_ = lean_box(0);
return v___x_702_;
}
else
{
lean_object* v_tail_703_; 
v_tail_703_ = lean_ctor_get(v_x_700_, 1);
if (lean_obj_tag(v_tail_703_) == 0)
{
lean_object* v_head_704_; lean_object* v___x_705_; 
lean_dec(v_x_701_);
v_head_704_ = lean_ctor_get(v_x_700_, 0);
lean_inc(v_head_704_);
lean_dec_ref_known(v_x_700_, 2);
v___x_705_ = l_Lean_instReprLeanOption_repr___redArg(v_head_704_);
return v___x_705_;
}
else
{
lean_object* v_head_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
lean_inc(v_tail_703_);
v_head_706_ = lean_ctor_get(v_x_700_, 0);
lean_inc(v_head_706_);
lean_dec_ref_known(v_x_700_, 2);
v___x_707_ = l_Lean_instReprLeanOption_repr___redArg(v_head_706_);
v___x_708_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_701_, v___x_707_, v_tail_703_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object* v_xs_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_710_ = lean_array_get_size(v_xs_709_);
v___x_711_ = lean_unsigned_to_nat(0u);
v___x_712_ = lean_nat_dec_eq(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_713_ = lean_array_to_list(v_xs_709_);
v___x_714_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_715_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_713_, v___x_714_);
v___x_716_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_717_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_718_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___x_715_);
v___x_719_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
v___x_721_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_716_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
v___x_722_ = l_Std_Format_fill(v___x_721_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; 
lean_dec_ref(v_xs_709_);
v___x_723_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
if (lean_obj_tag(v_x_726_) == 0)
{
lean_dec(v_x_724_);
return v_x_725_;
}
else
{
lean_object* v_head_727_; lean_object* v_tail_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_739_; 
v_head_727_ = lean_ctor_get(v_x_726_, 0);
v_tail_728_ = lean_ctor_get(v_x_726_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_x_726_);
if (v_isSharedCheck_739_ == 0)
{
v___x_730_ = v_x_726_;
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_tail_728_);
lean_inc(v_head_727_);
lean_dec(v_x_726_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_739_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
lean_inc(v_x_724_);
if (v_isShared_731_ == 0)
{
lean_ctor_set_tag(v___x_730_, 5);
lean_ctor_set(v___x_730_, 1, v_x_724_);
lean_ctor_set(v___x_730_, 0, v_x_725_);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_x_725_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_x_724_);
v___x_733_ = v_reuseFailAlloc_738_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = l_Lake_Target_repr___redArg(v_head_727_, v___x_734_);
v___x_736_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_733_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v_x_725_ = v___x_736_;
v_x_726_ = v_tail_728_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object* v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
if (lean_obj_tag(v_x_742_) == 0)
{
lean_dec(v_x_740_);
return v_x_741_;
}
else
{
lean_object* v_head_743_; lean_object* v_tail_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_755_; 
v_head_743_ = lean_ctor_get(v_x_742_, 0);
v_tail_744_ = lean_ctor_get(v_x_742_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_x_742_);
if (v_isSharedCheck_755_ == 0)
{
v___x_746_ = v_x_742_;
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_tail_744_);
lean_inc(v_head_743_);
lean_dec(v_x_742_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
lean_inc(v_x_740_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 5);
lean_ctor_set(v___x_746_, 1, v_x_740_);
lean_ctor_set(v___x_746_, 0, v_x_741_);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_x_741_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_x_740_);
v___x_749_ = v_reuseFailAlloc_754_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = l_Lake_Target_repr___redArg(v_head_743_, v___x_750_);
v___x_752_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_752_, 0, v___x_749_);
lean_ctor_set(v___x_752_, 1, v___x_751_);
v___x_753_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_740_, v___x_752_, v_tail_744_);
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
lean_object* v___x_758_; 
lean_dec(v_x_757_);
v___x_758_ = lean_box(0);
return v___x_758_;
}
else
{
lean_object* v_tail_759_; 
v_tail_759_ = lean_ctor_get(v_x_756_, 1);
if (lean_obj_tag(v_tail_759_) == 0)
{
lean_object* v_head_760_; lean_object* v___x_761_; 
lean_dec(v_x_757_);
v_head_760_ = lean_ctor_get(v_x_756_, 0);
lean_inc(v_head_760_);
lean_dec_ref_known(v_x_756_, 2);
v___x_761_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_760_);
return v___x_761_;
}
else
{
lean_object* v_head_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
lean_inc(v_tail_759_);
v_head_762_ = lean_ctor_get(v_x_756_, 0);
lean_inc(v_head_762_);
lean_dec_ref_known(v_x_756_, 2);
v___x_763_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_762_);
v___x_764_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_757_, v___x_763_, v_tail_759_);
return v___x_764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object* v_xs_765_){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_766_ = lean_array_get_size(v_xs_765_);
v___x_767_ = lean_unsigned_to_nat(0u);
v___x_768_ = lean_nat_dec_eq(v___x_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_769_ = lean_array_to_list(v_xs_765_);
v___x_770_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_771_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_769_, v___x_770_);
v___x_772_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_773_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_774_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_771_);
v___x_775_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_776_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_777_, 0, v___x_772_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Std_Format_fill(v___x_777_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; 
lean_dec_ref(v_xs_765_);
v___x_779_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_779_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_unsigned_to_nat(13u);
v___x_794_ = lean_nat_to_int(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(15u);
v___x_799_ = lean_nat_to_int(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_unsigned_to_nat(16u);
v___x_804_ = lean_nat_to_int(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_unsigned_to_nat(17u);
v___x_812_ = lean_nat_to_int(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_unsigned_to_nat(21u);
v___x_817_ = lean_nat_to_int(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(11u);
v___x_837_ = lean_nat_to_int(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(23u);
v___x_842_ = lean_nat_to_int(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = lean_unsigned_to_nat(24u);
v___x_853_ = lean_nat_to_int(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__47(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_unsigned_to_nat(19u);
v___x_858_ = lean_nat_to_int(v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_861_ = lean_string_length(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__50(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__49, &l_Lake_instReprLeanConfig_repr___redArg___closed__49_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49);
v___x_863_ = lean_nat_to_int(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_868_){
_start:
{
uint8_t v_buildType_869_; lean_object* v_leanOptions_870_; lean_object* v_moreLeanArgs_871_; lean_object* v_weakLeanArgs_872_; lean_object* v_moreLeancArgs_873_; lean_object* v_moreServerOptions_874_; lean_object* v_weakLeancArgs_875_; lean_object* v_moreLinkObjs_876_; lean_object* v_moreLinkLibs_877_; lean_object* v_moreLinkArgs_878_; lean_object* v_weakLinkArgs_879_; uint8_t v_backend_880_; lean_object* v_platformIndependent_881_; lean_object* v_dynlibs_882_; lean_object* v_plugins_883_; uint8_t v_requiresModuleSystem_884_; uint8_t v_allowNonModules_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_buildType_869_ = lean_ctor_get_uint8(v_x_868_, sizeof(void*)*13);
v_leanOptions_870_ = lean_ctor_get(v_x_868_, 0);
lean_inc_ref(v_leanOptions_870_);
v_moreLeanArgs_871_ = lean_ctor_get(v_x_868_, 1);
lean_inc_ref(v_moreLeanArgs_871_);
v_weakLeanArgs_872_ = lean_ctor_get(v_x_868_, 2);
lean_inc_ref(v_weakLeanArgs_872_);
v_moreLeancArgs_873_ = lean_ctor_get(v_x_868_, 3);
lean_inc_ref(v_moreLeancArgs_873_);
v_moreServerOptions_874_ = lean_ctor_get(v_x_868_, 4);
lean_inc_ref(v_moreServerOptions_874_);
v_weakLeancArgs_875_ = lean_ctor_get(v_x_868_, 5);
lean_inc_ref(v_weakLeancArgs_875_);
v_moreLinkObjs_876_ = lean_ctor_get(v_x_868_, 6);
lean_inc_ref(v_moreLinkObjs_876_);
v_moreLinkLibs_877_ = lean_ctor_get(v_x_868_, 7);
lean_inc_ref(v_moreLinkLibs_877_);
v_moreLinkArgs_878_ = lean_ctor_get(v_x_868_, 8);
lean_inc_ref(v_moreLinkArgs_878_);
v_weakLinkArgs_879_ = lean_ctor_get(v_x_868_, 9);
lean_inc_ref(v_weakLinkArgs_879_);
v_backend_880_ = lean_ctor_get_uint8(v_x_868_, sizeof(void*)*13 + 1);
v_platformIndependent_881_ = lean_ctor_get(v_x_868_, 10);
lean_inc(v_platformIndependent_881_);
v_dynlibs_882_ = lean_ctor_get(v_x_868_, 11);
lean_inc_ref(v_dynlibs_882_);
v_plugins_883_ = lean_ctor_get(v_x_868_, 12);
lean_inc_ref(v_plugins_883_);
v_requiresModuleSystem_884_ = lean_ctor_get_uint8(v_x_868_, sizeof(void*)*13 + 2);
v_allowNonModules_885_ = lean_ctor_get_uint8(v_x_868_, sizeof(void*)*13 + 3);
lean_dec_ref(v_x_868_);
v___x_886_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_887_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_888_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = l_Lake_instReprBuildType_repr(v_buildType_869_, v___x_889_);
v___x_891_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_888_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = 0;
v___x_893_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set_uint8(v___x_893_, sizeof(void*)*1, v___x_892_);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_887_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2));
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_box(1);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__9));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___x_886_);
v___x_902_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__10, &l_Lake_instReprLeanConfig_repr___redArg___closed__10_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10);
v___x_903_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_870_);
v___x_904_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set_uint8(v___x_905_, sizeof(void*)*1, v___x_892_);
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_901_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_895_);
v___x_908_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_897_);
v___x_909_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__12));
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_886_);
v___x_912_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__13, &l_Lake_instReprLeanConfig_repr___redArg___closed__13_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13);
v___x_913_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_871_);
v___x_914_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set_uint8(v___x_915_, sizeof(void*)*1, v___x_892_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_911_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_895_);
v___x_918_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v___x_897_);
v___x_919_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__15));
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_886_);
v___x_922_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_872_);
v___x_923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_912_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*1, v___x_892_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_921_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_895_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_897_);
v___x_928_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__17));
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_886_);
v___x_931_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__18, &l_Lake_instReprLeanConfig_repr___redArg___closed__18_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18);
v___x_932_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_873_);
v___x_933_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*1, v___x_892_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_930_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_895_);
v___x_937_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_897_);
v___x_938_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__20));
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_886_);
v___x_941_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__21, &l_Lake_instReprLeanConfig_repr___redArg___closed__21_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21);
v___x_942_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_874_);
v___x_943_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set_uint8(v___x_944_, sizeof(void*)*1, v___x_892_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_940_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_895_);
v___x_947_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_897_);
v___x_948_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__23));
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_947_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_886_);
v___x_951_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_875_);
v___x_952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_931_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_892_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_950_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_895_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_897_);
v___x_957_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__25));
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_886_);
v___x_960_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_876_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_912_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_892_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_895_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_897_);
v___x_966_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__27));
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_886_);
v___x_969_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_877_);
v___x_970_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_912_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*1, v___x_892_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_968_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_895_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_897_);
v___x_975_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__29));
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_886_);
v___x_978_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_878_);
v___x_979_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_912_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*1, v___x_892_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_977_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_895_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_897_);
v___x_984_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__31));
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_886_);
v___x_987_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_879_);
v___x_988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_912_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_892_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_986_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_895_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_897_);
v___x_993_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__33));
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_886_);
v___x_996_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__34, &l_Lake_instReprLeanConfig_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34);
v___x_997_ = l_Lake_instReprBackend_repr(v_backend_880_, v___x_889_);
v___x_998_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set_uint8(v___x_999_, sizeof(void*)*1, v___x_892_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_995_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_895_);
v___x_1002_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_897_);
v___x_1003_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__36));
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_886_);
v___x_1006_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__37, &l_Lake_instReprLeanConfig_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37);
v___x_1007_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_881_, v___x_889_);
lean_dec(v_platformIndependent_881_);
v___x_1008_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set_uint8(v___x_1009_, sizeof(void*)*1, v___x_892_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1005_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_895_);
v___x_1012_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_897_);
v___x_1013_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__39));
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_886_);
v___x_1016_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_882_);
v___x_1017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_996_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*1, v___x_892_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1015_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_895_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_897_);
v___x_1022_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__41));
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_886_);
v___x_1025_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_883_);
v___x_1026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_996_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*1, v___x_892_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_895_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_897_);
v___x_1031_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__43));
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_886_);
v___x_1034_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__44, &l_Lake_instReprLeanConfig_repr___redArg___closed__44_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44);
v___x_1035_ = l_Bool_repr___redArg(v_requiresModuleSystem_884_);
v___x_1036_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set_uint8(v___x_1037_, sizeof(void*)*1, v___x_892_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1033_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_895_);
v___x_1040_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v___x_897_);
v___x_1041_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__46));
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_886_);
v___x_1044_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__47, &l_Lake_instReprLeanConfig_repr___redArg___closed__47_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__47);
v___x_1045_ = l_Bool_repr___redArg(v_allowNonModules_885_);
v___x_1046_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set_uint8(v___x_1047_, sizeof(void*)*1, v___x_892_);
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1043_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__50, &l_Lake_instReprLeanConfig_repr___redArg___closed__50_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__50);
v___x_1050_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__51));
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_1048_);
v___x_1052_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__52));
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1049_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*1, v___x_892_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1056_, lean_object* v_prec_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1059_, lean_object* v_prec_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lake_instReprLeanConfig_repr(v_x_1059_, v_prec_1060_);
lean_dec(v_prec_1060_);
return v_res_1061_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1064_){
_start:
{
uint8_t v_buildType_1065_; 
v_buildType_1065_ = lean_ctor_get_uint8(v_cfg_1064_, sizeof(void*)*13);
return v_buildType_1065_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1066_);
lean_dec_ref(v_cfg_1066_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1069_, lean_object* v_cfg_1070_){
_start:
{
lean_object* v_leanOptions_1071_; lean_object* v_moreLeanArgs_1072_; lean_object* v_weakLeanArgs_1073_; lean_object* v_moreLeancArgs_1074_; lean_object* v_moreServerOptions_1075_; lean_object* v_weakLeancArgs_1076_; lean_object* v_moreLinkObjs_1077_; lean_object* v_moreLinkLibs_1078_; lean_object* v_moreLinkArgs_1079_; lean_object* v_weakLinkArgs_1080_; uint8_t v_backend_1081_; lean_object* v_platformIndependent_1082_; lean_object* v_dynlibs_1083_; lean_object* v_plugins_1084_; uint8_t v_requiresModuleSystem_1085_; uint8_t v_allowNonModules_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_leanOptions_1071_ = lean_ctor_get(v_cfg_1070_, 0);
v_moreLeanArgs_1072_ = lean_ctor_get(v_cfg_1070_, 1);
v_weakLeanArgs_1073_ = lean_ctor_get(v_cfg_1070_, 2);
v_moreLeancArgs_1074_ = lean_ctor_get(v_cfg_1070_, 3);
v_moreServerOptions_1075_ = lean_ctor_get(v_cfg_1070_, 4);
v_weakLeancArgs_1076_ = lean_ctor_get(v_cfg_1070_, 5);
v_moreLinkObjs_1077_ = lean_ctor_get(v_cfg_1070_, 6);
v_moreLinkLibs_1078_ = lean_ctor_get(v_cfg_1070_, 7);
v_moreLinkArgs_1079_ = lean_ctor_get(v_cfg_1070_, 8);
v_weakLinkArgs_1080_ = lean_ctor_get(v_cfg_1070_, 9);
v_backend_1081_ = lean_ctor_get_uint8(v_cfg_1070_, sizeof(void*)*13 + 1);
v_platformIndependent_1082_ = lean_ctor_get(v_cfg_1070_, 10);
v_dynlibs_1083_ = lean_ctor_get(v_cfg_1070_, 11);
v_plugins_1084_ = lean_ctor_get(v_cfg_1070_, 12);
v_requiresModuleSystem_1085_ = lean_ctor_get_uint8(v_cfg_1070_, sizeof(void*)*13 + 2);
v_allowNonModules_1086_ = lean_ctor_get_uint8(v_cfg_1070_, sizeof(void*)*13 + 3);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_cfg_1070_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v_cfg_1070_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_plugins_1084_);
lean_inc(v_dynlibs_1083_);
lean_inc(v_platformIndependent_1082_);
lean_inc(v_weakLinkArgs_1080_);
lean_inc(v_moreLinkArgs_1079_);
lean_inc(v_moreLinkLibs_1078_);
lean_inc(v_moreLinkObjs_1077_);
lean_inc(v_weakLeancArgs_1076_);
lean_inc(v_moreServerOptions_1075_);
lean_inc(v_moreLeancArgs_1074_);
lean_inc(v_weakLeanArgs_1073_);
lean_inc(v_moreLeanArgs_1072_);
lean_inc(v_leanOptions_1071_);
lean_dec(v_cfg_1070_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_leanOptions_1071_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_moreLeanArgs_1072_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_weakLeanArgs_1073_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_moreLeancArgs_1074_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_moreServerOptions_1075_);
lean_ctor_set(v_reuseFailAlloc_1092_, 5, v_weakLeancArgs_1076_);
lean_ctor_set(v_reuseFailAlloc_1092_, 6, v_moreLinkObjs_1077_);
lean_ctor_set(v_reuseFailAlloc_1092_, 7, v_moreLinkLibs_1078_);
lean_ctor_set(v_reuseFailAlloc_1092_, 8, v_moreLinkArgs_1079_);
lean_ctor_set(v_reuseFailAlloc_1092_, 9, v_weakLinkArgs_1080_);
lean_ctor_set(v_reuseFailAlloc_1092_, 10, v_platformIndependent_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 11, v_dynlibs_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 12, v_plugins_1084_);
lean_ctor_set_uint8(v_reuseFailAlloc_1092_, sizeof(void*)*13 + 1, v_backend_1081_);
lean_ctor_set_uint8(v_reuseFailAlloc_1092_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1085_);
lean_ctor_set_uint8(v_reuseFailAlloc_1092_, sizeof(void*)*13 + 3, v_allowNonModules_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
lean_ctor_set_uint8(v___x_1091_, sizeof(void*)*13, v_val_1069_);
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1094_, lean_object* v_cfg_1095_){
_start:
{
uint8_t v_val_85__boxed_1096_; lean_object* v_res_1097_; 
v_val_85__boxed_1096_ = lean_unbox(v_val_1094_);
v_res_1097_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_85__boxed_1096_, v_cfg_1095_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1098_, lean_object* v_cfg_1099_){
_start:
{
uint8_t v_buildType_1100_; lean_object* v_leanOptions_1101_; lean_object* v_moreLeanArgs_1102_; lean_object* v_weakLeanArgs_1103_; lean_object* v_moreLeancArgs_1104_; lean_object* v_moreServerOptions_1105_; lean_object* v_weakLeancArgs_1106_; lean_object* v_moreLinkObjs_1107_; lean_object* v_moreLinkLibs_1108_; lean_object* v_moreLinkArgs_1109_; lean_object* v_weakLinkArgs_1110_; uint8_t v_backend_1111_; lean_object* v_platformIndependent_1112_; lean_object* v_dynlibs_1113_; lean_object* v_plugins_1114_; uint8_t v_requiresModuleSystem_1115_; uint8_t v_allowNonModules_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1126_; 
v_buildType_1100_ = lean_ctor_get_uint8(v_cfg_1099_, sizeof(void*)*13);
v_leanOptions_1101_ = lean_ctor_get(v_cfg_1099_, 0);
v_moreLeanArgs_1102_ = lean_ctor_get(v_cfg_1099_, 1);
v_weakLeanArgs_1103_ = lean_ctor_get(v_cfg_1099_, 2);
v_moreLeancArgs_1104_ = lean_ctor_get(v_cfg_1099_, 3);
v_moreServerOptions_1105_ = lean_ctor_get(v_cfg_1099_, 4);
v_weakLeancArgs_1106_ = lean_ctor_get(v_cfg_1099_, 5);
v_moreLinkObjs_1107_ = lean_ctor_get(v_cfg_1099_, 6);
v_moreLinkLibs_1108_ = lean_ctor_get(v_cfg_1099_, 7);
v_moreLinkArgs_1109_ = lean_ctor_get(v_cfg_1099_, 8);
v_weakLinkArgs_1110_ = lean_ctor_get(v_cfg_1099_, 9);
v_backend_1111_ = lean_ctor_get_uint8(v_cfg_1099_, sizeof(void*)*13 + 1);
v_platformIndependent_1112_ = lean_ctor_get(v_cfg_1099_, 10);
v_dynlibs_1113_ = lean_ctor_get(v_cfg_1099_, 11);
v_plugins_1114_ = lean_ctor_get(v_cfg_1099_, 12);
v_requiresModuleSystem_1115_ = lean_ctor_get_uint8(v_cfg_1099_, sizeof(void*)*13 + 2);
v_allowNonModules_1116_ = lean_ctor_get_uint8(v_cfg_1099_, sizeof(void*)*13 + 3);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_cfg_1099_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1118_ = v_cfg_1099_;
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_plugins_1114_);
lean_inc(v_dynlibs_1113_);
lean_inc(v_platformIndependent_1112_);
lean_inc(v_weakLinkArgs_1110_);
lean_inc(v_moreLinkArgs_1109_);
lean_inc(v_moreLinkLibs_1108_);
lean_inc(v_moreLinkObjs_1107_);
lean_inc(v_weakLeancArgs_1106_);
lean_inc(v_moreServerOptions_1105_);
lean_inc(v_moreLeancArgs_1104_);
lean_inc(v_weakLeanArgs_1103_);
lean_inc(v_moreLeanArgs_1102_);
lean_inc(v_leanOptions_1101_);
lean_dec(v_cfg_1099_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1126_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1120_ = lean_box(v_buildType_1100_);
v___x_1121_ = lean_apply_1(v_f_1098_, v___x_1120_);
if (v_isShared_1119_ == 0)
{
v___x_1123_ = v___x_1118_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_leanOptions_1101_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_moreLeanArgs_1102_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_weakLeanArgs_1103_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_moreLeancArgs_1104_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v_moreServerOptions_1105_);
lean_ctor_set(v_reuseFailAlloc_1125_, 5, v_weakLeancArgs_1106_);
lean_ctor_set(v_reuseFailAlloc_1125_, 6, v_moreLinkObjs_1107_);
lean_ctor_set(v_reuseFailAlloc_1125_, 7, v_moreLinkLibs_1108_);
lean_ctor_set(v_reuseFailAlloc_1125_, 8, v_moreLinkArgs_1109_);
lean_ctor_set(v_reuseFailAlloc_1125_, 9, v_weakLinkArgs_1110_);
lean_ctor_set(v_reuseFailAlloc_1125_, 10, v_platformIndependent_1112_);
lean_ctor_set(v_reuseFailAlloc_1125_, 11, v_dynlibs_1113_);
lean_ctor_set(v_reuseFailAlloc_1125_, 12, v_plugins_1114_);
v___x_1123_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_unbox(v___x_1121_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*13, v___x_1124_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*13 + 1, v_backend_1111_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1115_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*13 + 3, v_allowNonModules_1116_);
return v___x_1123_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1127_){
_start:
{
uint8_t v___x_1128_; 
v___x_1128_ = 3;
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1129_);
lean_dec_ref(v_x_1129_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1143_){
_start:
{
lean_object* v_leanOptions_1144_; 
v_leanOptions_1144_ = lean_ctor_get(v_cfg_1143_, 0);
lean_inc_ref(v_leanOptions_1144_);
return v_leanOptions_1144_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1145_);
lean_dec_ref(v_cfg_1145_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1147_, lean_object* v_cfg_1148_){
_start:
{
uint8_t v_buildType_1149_; lean_object* v_moreLeanArgs_1150_; lean_object* v_weakLeanArgs_1151_; lean_object* v_moreLeancArgs_1152_; lean_object* v_moreServerOptions_1153_; lean_object* v_weakLeancArgs_1154_; lean_object* v_moreLinkObjs_1155_; lean_object* v_moreLinkLibs_1156_; lean_object* v_moreLinkArgs_1157_; lean_object* v_weakLinkArgs_1158_; uint8_t v_backend_1159_; lean_object* v_platformIndependent_1160_; lean_object* v_dynlibs_1161_; lean_object* v_plugins_1162_; uint8_t v_requiresModuleSystem_1163_; uint8_t v_allowNonModules_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_buildType_1149_ = lean_ctor_get_uint8(v_cfg_1148_, sizeof(void*)*13);
v_moreLeanArgs_1150_ = lean_ctor_get(v_cfg_1148_, 1);
v_weakLeanArgs_1151_ = lean_ctor_get(v_cfg_1148_, 2);
v_moreLeancArgs_1152_ = lean_ctor_get(v_cfg_1148_, 3);
v_moreServerOptions_1153_ = lean_ctor_get(v_cfg_1148_, 4);
v_weakLeancArgs_1154_ = lean_ctor_get(v_cfg_1148_, 5);
v_moreLinkObjs_1155_ = lean_ctor_get(v_cfg_1148_, 6);
v_moreLinkLibs_1156_ = lean_ctor_get(v_cfg_1148_, 7);
v_moreLinkArgs_1157_ = lean_ctor_get(v_cfg_1148_, 8);
v_weakLinkArgs_1158_ = lean_ctor_get(v_cfg_1148_, 9);
v_backend_1159_ = lean_ctor_get_uint8(v_cfg_1148_, sizeof(void*)*13 + 1);
v_platformIndependent_1160_ = lean_ctor_get(v_cfg_1148_, 10);
v_dynlibs_1161_ = lean_ctor_get(v_cfg_1148_, 11);
v_plugins_1162_ = lean_ctor_get(v_cfg_1148_, 12);
v_requiresModuleSystem_1163_ = lean_ctor_get_uint8(v_cfg_1148_, sizeof(void*)*13 + 2);
v_allowNonModules_1164_ = lean_ctor_get_uint8(v_cfg_1148_, sizeof(void*)*13 + 3);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_cfg_1148_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v_cfg_1148_, 0);
lean_dec(v_unused_1172_);
v___x_1166_ = v_cfg_1148_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_plugins_1162_);
lean_inc(v_dynlibs_1161_);
lean_inc(v_platformIndependent_1160_);
lean_inc(v_weakLinkArgs_1158_);
lean_inc(v_moreLinkArgs_1157_);
lean_inc(v_moreLinkLibs_1156_);
lean_inc(v_moreLinkObjs_1155_);
lean_inc(v_weakLeancArgs_1154_);
lean_inc(v_moreServerOptions_1153_);
lean_inc(v_moreLeancArgs_1152_);
lean_inc(v_weakLeanArgs_1151_);
lean_inc(v_moreLeanArgs_1150_);
lean_dec(v_cfg_1148_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v_val_1147_);
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_val_1147_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_moreLeanArgs_1150_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_weakLeanArgs_1151_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_moreLeancArgs_1152_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_moreServerOptions_1153_);
lean_ctor_set(v_reuseFailAlloc_1170_, 5, v_weakLeancArgs_1154_);
lean_ctor_set(v_reuseFailAlloc_1170_, 6, v_moreLinkObjs_1155_);
lean_ctor_set(v_reuseFailAlloc_1170_, 7, v_moreLinkLibs_1156_);
lean_ctor_set(v_reuseFailAlloc_1170_, 8, v_moreLinkArgs_1157_);
lean_ctor_set(v_reuseFailAlloc_1170_, 9, v_weakLinkArgs_1158_);
lean_ctor_set(v_reuseFailAlloc_1170_, 10, v_platformIndependent_1160_);
lean_ctor_set(v_reuseFailAlloc_1170_, 11, v_dynlibs_1161_);
lean_ctor_set(v_reuseFailAlloc_1170_, 12, v_plugins_1162_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*13, v_buildType_1149_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*13 + 1, v_backend_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1163_);
lean_ctor_set_uint8(v_reuseFailAlloc_1170_, sizeof(void*)*13 + 3, v_allowNonModules_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1173_, lean_object* v_cfg_1174_){
_start:
{
uint8_t v_buildType_1175_; lean_object* v_leanOptions_1176_; lean_object* v_moreLeanArgs_1177_; lean_object* v_weakLeanArgs_1178_; lean_object* v_moreLeancArgs_1179_; lean_object* v_moreServerOptions_1180_; lean_object* v_weakLeancArgs_1181_; lean_object* v_moreLinkObjs_1182_; lean_object* v_moreLinkLibs_1183_; lean_object* v_moreLinkArgs_1184_; lean_object* v_weakLinkArgs_1185_; uint8_t v_backend_1186_; lean_object* v_platformIndependent_1187_; lean_object* v_dynlibs_1188_; lean_object* v_plugins_1189_; uint8_t v_requiresModuleSystem_1190_; uint8_t v_allowNonModules_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1199_; 
v_buildType_1175_ = lean_ctor_get_uint8(v_cfg_1174_, sizeof(void*)*13);
v_leanOptions_1176_ = lean_ctor_get(v_cfg_1174_, 0);
v_moreLeanArgs_1177_ = lean_ctor_get(v_cfg_1174_, 1);
v_weakLeanArgs_1178_ = lean_ctor_get(v_cfg_1174_, 2);
v_moreLeancArgs_1179_ = lean_ctor_get(v_cfg_1174_, 3);
v_moreServerOptions_1180_ = lean_ctor_get(v_cfg_1174_, 4);
v_weakLeancArgs_1181_ = lean_ctor_get(v_cfg_1174_, 5);
v_moreLinkObjs_1182_ = lean_ctor_get(v_cfg_1174_, 6);
v_moreLinkLibs_1183_ = lean_ctor_get(v_cfg_1174_, 7);
v_moreLinkArgs_1184_ = lean_ctor_get(v_cfg_1174_, 8);
v_weakLinkArgs_1185_ = lean_ctor_get(v_cfg_1174_, 9);
v_backend_1186_ = lean_ctor_get_uint8(v_cfg_1174_, sizeof(void*)*13 + 1);
v_platformIndependent_1187_ = lean_ctor_get(v_cfg_1174_, 10);
v_dynlibs_1188_ = lean_ctor_get(v_cfg_1174_, 11);
v_plugins_1189_ = lean_ctor_get(v_cfg_1174_, 12);
v_requiresModuleSystem_1190_ = lean_ctor_get_uint8(v_cfg_1174_, sizeof(void*)*13 + 2);
v_allowNonModules_1191_ = lean_ctor_get_uint8(v_cfg_1174_, sizeof(void*)*13 + 3);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_cfg_1174_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1193_ = v_cfg_1174_;
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_plugins_1189_);
lean_inc(v_dynlibs_1188_);
lean_inc(v_platformIndependent_1187_);
lean_inc(v_weakLinkArgs_1185_);
lean_inc(v_moreLinkArgs_1184_);
lean_inc(v_moreLinkLibs_1183_);
lean_inc(v_moreLinkObjs_1182_);
lean_inc(v_weakLeancArgs_1181_);
lean_inc(v_moreServerOptions_1180_);
lean_inc(v_moreLeancArgs_1179_);
lean_inc(v_weakLeanArgs_1178_);
lean_inc(v_moreLeanArgs_1177_);
lean_inc(v_leanOptions_1176_);
lean_dec(v_cfg_1174_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1199_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1195_ = lean_apply_1(v_f_1173_, v_leanOptions_1176_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1195_);
v___x_1197_ = v___x_1193_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_moreLeanArgs_1177_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_weakLeanArgs_1178_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_moreLeancArgs_1179_);
lean_ctor_set(v_reuseFailAlloc_1198_, 4, v_moreServerOptions_1180_);
lean_ctor_set(v_reuseFailAlloc_1198_, 5, v_weakLeancArgs_1181_);
lean_ctor_set(v_reuseFailAlloc_1198_, 6, v_moreLinkObjs_1182_);
lean_ctor_set(v_reuseFailAlloc_1198_, 7, v_moreLinkLibs_1183_);
lean_ctor_set(v_reuseFailAlloc_1198_, 8, v_moreLinkArgs_1184_);
lean_ctor_set(v_reuseFailAlloc_1198_, 9, v_weakLinkArgs_1185_);
lean_ctor_set(v_reuseFailAlloc_1198_, 10, v_platformIndependent_1187_);
lean_ctor_set(v_reuseFailAlloc_1198_, 11, v_dynlibs_1188_);
lean_ctor_set(v_reuseFailAlloc_1198_, 12, v_plugins_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*13, v_buildType_1175_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*13 + 1, v_backend_1186_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1190_);
lean_ctor_set_uint8(v_reuseFailAlloc_1198_, sizeof(void*)*13 + 3, v_allowNonModules_1191_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1202_);
lean_dec_ref(v_x_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1215_){
_start:
{
lean_object* v_moreLeanArgs_1216_; 
v_moreLeanArgs_1216_ = lean_ctor_get(v_cfg_1215_, 1);
lean_inc_ref(v_moreLeanArgs_1216_);
return v_moreLeanArgs_1216_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1217_);
lean_dec_ref(v_cfg_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1219_, lean_object* v_cfg_1220_){
_start:
{
uint8_t v_buildType_1221_; lean_object* v_leanOptions_1222_; lean_object* v_weakLeanArgs_1223_; lean_object* v_moreLeancArgs_1224_; lean_object* v_moreServerOptions_1225_; lean_object* v_weakLeancArgs_1226_; lean_object* v_moreLinkObjs_1227_; lean_object* v_moreLinkLibs_1228_; lean_object* v_moreLinkArgs_1229_; lean_object* v_weakLinkArgs_1230_; uint8_t v_backend_1231_; lean_object* v_platformIndependent_1232_; lean_object* v_dynlibs_1233_; lean_object* v_plugins_1234_; uint8_t v_requiresModuleSystem_1235_; uint8_t v_allowNonModules_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
v_buildType_1221_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*13);
v_leanOptions_1222_ = lean_ctor_get(v_cfg_1220_, 0);
v_weakLeanArgs_1223_ = lean_ctor_get(v_cfg_1220_, 2);
v_moreLeancArgs_1224_ = lean_ctor_get(v_cfg_1220_, 3);
v_moreServerOptions_1225_ = lean_ctor_get(v_cfg_1220_, 4);
v_weakLeancArgs_1226_ = lean_ctor_get(v_cfg_1220_, 5);
v_moreLinkObjs_1227_ = lean_ctor_get(v_cfg_1220_, 6);
v_moreLinkLibs_1228_ = lean_ctor_get(v_cfg_1220_, 7);
v_moreLinkArgs_1229_ = lean_ctor_get(v_cfg_1220_, 8);
v_weakLinkArgs_1230_ = lean_ctor_get(v_cfg_1220_, 9);
v_backend_1231_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*13 + 1);
v_platformIndependent_1232_ = lean_ctor_get(v_cfg_1220_, 10);
v_dynlibs_1233_ = lean_ctor_get(v_cfg_1220_, 11);
v_plugins_1234_ = lean_ctor_get(v_cfg_1220_, 12);
v_requiresModuleSystem_1235_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*13 + 2);
v_allowNonModules_1236_ = lean_ctor_get_uint8(v_cfg_1220_, sizeof(void*)*13 + 3);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_cfg_1220_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v_cfg_1220_, 1);
lean_dec(v_unused_1244_);
v___x_1238_ = v_cfg_1220_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_plugins_1234_);
lean_inc(v_dynlibs_1233_);
lean_inc(v_platformIndependent_1232_);
lean_inc(v_weakLinkArgs_1230_);
lean_inc(v_moreLinkArgs_1229_);
lean_inc(v_moreLinkLibs_1228_);
lean_inc(v_moreLinkObjs_1227_);
lean_inc(v_weakLeancArgs_1226_);
lean_inc(v_moreServerOptions_1225_);
lean_inc(v_moreLeancArgs_1224_);
lean_inc(v_weakLeanArgs_1223_);
lean_inc(v_leanOptions_1222_);
lean_dec(v_cfg_1220_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v_val_1219_);
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_leanOptions_1222_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_val_1219_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_weakLeanArgs_1223_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_moreLeancArgs_1224_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_moreServerOptions_1225_);
lean_ctor_set(v_reuseFailAlloc_1242_, 5, v_weakLeancArgs_1226_);
lean_ctor_set(v_reuseFailAlloc_1242_, 6, v_moreLinkObjs_1227_);
lean_ctor_set(v_reuseFailAlloc_1242_, 7, v_moreLinkLibs_1228_);
lean_ctor_set(v_reuseFailAlloc_1242_, 8, v_moreLinkArgs_1229_);
lean_ctor_set(v_reuseFailAlloc_1242_, 9, v_weakLinkArgs_1230_);
lean_ctor_set(v_reuseFailAlloc_1242_, 10, v_platformIndependent_1232_);
lean_ctor_set(v_reuseFailAlloc_1242_, 11, v_dynlibs_1233_);
lean_ctor_set(v_reuseFailAlloc_1242_, 12, v_plugins_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*13, v_buildType_1221_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*13 + 1, v_backend_1231_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1235_);
lean_ctor_set_uint8(v_reuseFailAlloc_1242_, sizeof(void*)*13 + 3, v_allowNonModules_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1245_, lean_object* v_cfg_1246_){
_start:
{
uint8_t v_buildType_1247_; lean_object* v_leanOptions_1248_; lean_object* v_moreLeanArgs_1249_; lean_object* v_weakLeanArgs_1250_; lean_object* v_moreLeancArgs_1251_; lean_object* v_moreServerOptions_1252_; lean_object* v_weakLeancArgs_1253_; lean_object* v_moreLinkObjs_1254_; lean_object* v_moreLinkLibs_1255_; lean_object* v_moreLinkArgs_1256_; lean_object* v_weakLinkArgs_1257_; uint8_t v_backend_1258_; lean_object* v_platformIndependent_1259_; lean_object* v_dynlibs_1260_; lean_object* v_plugins_1261_; uint8_t v_requiresModuleSystem_1262_; uint8_t v_allowNonModules_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_buildType_1247_ = lean_ctor_get_uint8(v_cfg_1246_, sizeof(void*)*13);
v_leanOptions_1248_ = lean_ctor_get(v_cfg_1246_, 0);
v_moreLeanArgs_1249_ = lean_ctor_get(v_cfg_1246_, 1);
v_weakLeanArgs_1250_ = lean_ctor_get(v_cfg_1246_, 2);
v_moreLeancArgs_1251_ = lean_ctor_get(v_cfg_1246_, 3);
v_moreServerOptions_1252_ = lean_ctor_get(v_cfg_1246_, 4);
v_weakLeancArgs_1253_ = lean_ctor_get(v_cfg_1246_, 5);
v_moreLinkObjs_1254_ = lean_ctor_get(v_cfg_1246_, 6);
v_moreLinkLibs_1255_ = lean_ctor_get(v_cfg_1246_, 7);
v_moreLinkArgs_1256_ = lean_ctor_get(v_cfg_1246_, 8);
v_weakLinkArgs_1257_ = lean_ctor_get(v_cfg_1246_, 9);
v_backend_1258_ = lean_ctor_get_uint8(v_cfg_1246_, sizeof(void*)*13 + 1);
v_platformIndependent_1259_ = lean_ctor_get(v_cfg_1246_, 10);
v_dynlibs_1260_ = lean_ctor_get(v_cfg_1246_, 11);
v_plugins_1261_ = lean_ctor_get(v_cfg_1246_, 12);
v_requiresModuleSystem_1262_ = lean_ctor_get_uint8(v_cfg_1246_, sizeof(void*)*13 + 2);
v_allowNonModules_1263_ = lean_ctor_get_uint8(v_cfg_1246_, sizeof(void*)*13 + 3);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_cfg_1246_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v_cfg_1246_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_plugins_1261_);
lean_inc(v_dynlibs_1260_);
lean_inc(v_platformIndependent_1259_);
lean_inc(v_weakLinkArgs_1257_);
lean_inc(v_moreLinkArgs_1256_);
lean_inc(v_moreLinkLibs_1255_);
lean_inc(v_moreLinkObjs_1254_);
lean_inc(v_weakLeancArgs_1253_);
lean_inc(v_moreServerOptions_1252_);
lean_inc(v_moreLeancArgs_1251_);
lean_inc(v_weakLeanArgs_1250_);
lean_inc(v_moreLeanArgs_1249_);
lean_inc(v_leanOptions_1248_);
lean_dec(v_cfg_1246_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_apply_1(v_f_1245_, v_moreLeanArgs_1249_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v___x_1267_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_leanOptions_1248_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_weakLeanArgs_1250_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_moreLeancArgs_1251_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_moreServerOptions_1252_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v_weakLeancArgs_1253_);
lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_moreLinkObjs_1254_);
lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_moreLinkLibs_1255_);
lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_moreLinkArgs_1256_);
lean_ctor_set(v_reuseFailAlloc_1270_, 9, v_weakLinkArgs_1257_);
lean_ctor_set(v_reuseFailAlloc_1270_, 10, v_platformIndependent_1259_);
lean_ctor_set(v_reuseFailAlloc_1270_, 11, v_dynlibs_1260_);
lean_ctor_set(v_reuseFailAlloc_1270_, 12, v_plugins_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13, v_buildType_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 1, v_backend_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1270_, sizeof(void*)*13 + 3, v_allowNonModules_1263_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1272_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1274_);
lean_dec_ref(v_x_1274_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1287_){
_start:
{
lean_object* v_weakLeanArgs_1288_; 
v_weakLeanArgs_1288_ = lean_ctor_get(v_cfg_1287_, 2);
lean_inc_ref(v_weakLeanArgs_1288_);
return v_weakLeanArgs_1288_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1289_);
lean_dec_ref(v_cfg_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1291_, lean_object* v_cfg_1292_){
_start:
{
uint8_t v_buildType_1293_; lean_object* v_leanOptions_1294_; lean_object* v_moreLeanArgs_1295_; lean_object* v_moreLeancArgs_1296_; lean_object* v_moreServerOptions_1297_; lean_object* v_weakLeancArgs_1298_; lean_object* v_moreLinkObjs_1299_; lean_object* v_moreLinkLibs_1300_; lean_object* v_moreLinkArgs_1301_; lean_object* v_weakLinkArgs_1302_; uint8_t v_backend_1303_; lean_object* v_platformIndependent_1304_; lean_object* v_dynlibs_1305_; lean_object* v_plugins_1306_; uint8_t v_requiresModuleSystem_1307_; uint8_t v_allowNonModules_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
v_buildType_1293_ = lean_ctor_get_uint8(v_cfg_1292_, sizeof(void*)*13);
v_leanOptions_1294_ = lean_ctor_get(v_cfg_1292_, 0);
v_moreLeanArgs_1295_ = lean_ctor_get(v_cfg_1292_, 1);
v_moreLeancArgs_1296_ = lean_ctor_get(v_cfg_1292_, 3);
v_moreServerOptions_1297_ = lean_ctor_get(v_cfg_1292_, 4);
v_weakLeancArgs_1298_ = lean_ctor_get(v_cfg_1292_, 5);
v_moreLinkObjs_1299_ = lean_ctor_get(v_cfg_1292_, 6);
v_moreLinkLibs_1300_ = lean_ctor_get(v_cfg_1292_, 7);
v_moreLinkArgs_1301_ = lean_ctor_get(v_cfg_1292_, 8);
v_weakLinkArgs_1302_ = lean_ctor_get(v_cfg_1292_, 9);
v_backend_1303_ = lean_ctor_get_uint8(v_cfg_1292_, sizeof(void*)*13 + 1);
v_platformIndependent_1304_ = lean_ctor_get(v_cfg_1292_, 10);
v_dynlibs_1305_ = lean_ctor_get(v_cfg_1292_, 11);
v_plugins_1306_ = lean_ctor_get(v_cfg_1292_, 12);
v_requiresModuleSystem_1307_ = lean_ctor_get_uint8(v_cfg_1292_, sizeof(void*)*13 + 2);
v_allowNonModules_1308_ = lean_ctor_get_uint8(v_cfg_1292_, sizeof(void*)*13 + 3);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_cfg_1292_);
if (v_isSharedCheck_1315_ == 0)
{
lean_object* v_unused_1316_; 
v_unused_1316_ = lean_ctor_get(v_cfg_1292_, 2);
lean_dec(v_unused_1316_);
v___x_1310_ = v_cfg_1292_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_plugins_1306_);
lean_inc(v_dynlibs_1305_);
lean_inc(v_platformIndependent_1304_);
lean_inc(v_weakLinkArgs_1302_);
lean_inc(v_moreLinkArgs_1301_);
lean_inc(v_moreLinkLibs_1300_);
lean_inc(v_moreLinkObjs_1299_);
lean_inc(v_weakLeancArgs_1298_);
lean_inc(v_moreServerOptions_1297_);
lean_inc(v_moreLeancArgs_1296_);
lean_inc(v_moreLeanArgs_1295_);
lean_inc(v_leanOptions_1294_);
lean_dec(v_cfg_1292_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 2, v_val_1291_);
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_leanOptions_1294_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_moreLeanArgs_1295_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_val_1291_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_moreLeancArgs_1296_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_moreServerOptions_1297_);
lean_ctor_set(v_reuseFailAlloc_1314_, 5, v_weakLeancArgs_1298_);
lean_ctor_set(v_reuseFailAlloc_1314_, 6, v_moreLinkObjs_1299_);
lean_ctor_set(v_reuseFailAlloc_1314_, 7, v_moreLinkLibs_1300_);
lean_ctor_set(v_reuseFailAlloc_1314_, 8, v_moreLinkArgs_1301_);
lean_ctor_set(v_reuseFailAlloc_1314_, 9, v_weakLinkArgs_1302_);
lean_ctor_set(v_reuseFailAlloc_1314_, 10, v_platformIndependent_1304_);
lean_ctor_set(v_reuseFailAlloc_1314_, 11, v_dynlibs_1305_);
lean_ctor_set(v_reuseFailAlloc_1314_, 12, v_plugins_1306_);
lean_ctor_set_uint8(v_reuseFailAlloc_1314_, sizeof(void*)*13, v_buildType_1293_);
lean_ctor_set_uint8(v_reuseFailAlloc_1314_, sizeof(void*)*13 + 1, v_backend_1303_);
lean_ctor_set_uint8(v_reuseFailAlloc_1314_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1307_);
lean_ctor_set_uint8(v_reuseFailAlloc_1314_, sizeof(void*)*13 + 3, v_allowNonModules_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1317_, lean_object* v_cfg_1318_){
_start:
{
uint8_t v_buildType_1319_; lean_object* v_leanOptions_1320_; lean_object* v_moreLeanArgs_1321_; lean_object* v_weakLeanArgs_1322_; lean_object* v_moreLeancArgs_1323_; lean_object* v_moreServerOptions_1324_; lean_object* v_weakLeancArgs_1325_; lean_object* v_moreLinkObjs_1326_; lean_object* v_moreLinkLibs_1327_; lean_object* v_moreLinkArgs_1328_; lean_object* v_weakLinkArgs_1329_; uint8_t v_backend_1330_; lean_object* v_platformIndependent_1331_; lean_object* v_dynlibs_1332_; lean_object* v_plugins_1333_; uint8_t v_requiresModuleSystem_1334_; uint8_t v_allowNonModules_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1343_; 
v_buildType_1319_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13);
v_leanOptions_1320_ = lean_ctor_get(v_cfg_1318_, 0);
v_moreLeanArgs_1321_ = lean_ctor_get(v_cfg_1318_, 1);
v_weakLeanArgs_1322_ = lean_ctor_get(v_cfg_1318_, 2);
v_moreLeancArgs_1323_ = lean_ctor_get(v_cfg_1318_, 3);
v_moreServerOptions_1324_ = lean_ctor_get(v_cfg_1318_, 4);
v_weakLeancArgs_1325_ = lean_ctor_get(v_cfg_1318_, 5);
v_moreLinkObjs_1326_ = lean_ctor_get(v_cfg_1318_, 6);
v_moreLinkLibs_1327_ = lean_ctor_get(v_cfg_1318_, 7);
v_moreLinkArgs_1328_ = lean_ctor_get(v_cfg_1318_, 8);
v_weakLinkArgs_1329_ = lean_ctor_get(v_cfg_1318_, 9);
v_backend_1330_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13 + 1);
v_platformIndependent_1331_ = lean_ctor_get(v_cfg_1318_, 10);
v_dynlibs_1332_ = lean_ctor_get(v_cfg_1318_, 11);
v_plugins_1333_ = lean_ctor_get(v_cfg_1318_, 12);
v_requiresModuleSystem_1334_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13 + 2);
v_allowNonModules_1335_ = lean_ctor_get_uint8(v_cfg_1318_, sizeof(void*)*13 + 3);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_cfg_1318_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1337_ = v_cfg_1318_;
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_plugins_1333_);
lean_inc(v_dynlibs_1332_);
lean_inc(v_platformIndependent_1331_);
lean_inc(v_weakLinkArgs_1329_);
lean_inc(v_moreLinkArgs_1328_);
lean_inc(v_moreLinkLibs_1327_);
lean_inc(v_moreLinkObjs_1326_);
lean_inc(v_weakLeancArgs_1325_);
lean_inc(v_moreServerOptions_1324_);
lean_inc(v_moreLeancArgs_1323_);
lean_inc(v_weakLeanArgs_1322_);
lean_inc(v_moreLeanArgs_1321_);
lean_inc(v_leanOptions_1320_);
lean_dec(v_cfg_1318_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1343_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1339_ = lean_apply_1(v_f_1317_, v_weakLeanArgs_1322_);
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 2, v___x_1339_);
v___x_1341_ = v___x_1337_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_leanOptions_1320_);
lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_moreLeanArgs_1321_);
lean_ctor_set(v_reuseFailAlloc_1342_, 2, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1342_, 3, v_moreLeancArgs_1323_);
lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_moreServerOptions_1324_);
lean_ctor_set(v_reuseFailAlloc_1342_, 5, v_weakLeancArgs_1325_);
lean_ctor_set(v_reuseFailAlloc_1342_, 6, v_moreLinkObjs_1326_);
lean_ctor_set(v_reuseFailAlloc_1342_, 7, v_moreLinkLibs_1327_);
lean_ctor_set(v_reuseFailAlloc_1342_, 8, v_moreLinkArgs_1328_);
lean_ctor_set(v_reuseFailAlloc_1342_, 9, v_weakLinkArgs_1329_);
lean_ctor_set(v_reuseFailAlloc_1342_, 10, v_platformIndependent_1331_);
lean_ctor_set(v_reuseFailAlloc_1342_, 11, v_dynlibs_1332_);
lean_ctor_set(v_reuseFailAlloc_1342_, 12, v_plugins_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*13, v_buildType_1319_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*13 + 1, v_backend_1330_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1334_);
lean_ctor_set_uint8(v_reuseFailAlloc_1342_, sizeof(void*)*13 + 3, v_allowNonModules_1335_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1354_){
_start:
{
lean_object* v_moreLeancArgs_1355_; 
v_moreLeancArgs_1355_ = lean_ctor_get(v_cfg_1354_, 3);
lean_inc_ref(v_moreLeancArgs_1355_);
return v_moreLeancArgs_1355_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1356_);
lean_dec_ref(v_cfg_1356_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1358_, lean_object* v_cfg_1359_){
_start:
{
uint8_t v_buildType_1360_; lean_object* v_leanOptions_1361_; lean_object* v_moreLeanArgs_1362_; lean_object* v_weakLeanArgs_1363_; lean_object* v_moreServerOptions_1364_; lean_object* v_weakLeancArgs_1365_; lean_object* v_moreLinkObjs_1366_; lean_object* v_moreLinkLibs_1367_; lean_object* v_moreLinkArgs_1368_; lean_object* v_weakLinkArgs_1369_; uint8_t v_backend_1370_; lean_object* v_platformIndependent_1371_; lean_object* v_dynlibs_1372_; lean_object* v_plugins_1373_; uint8_t v_requiresModuleSystem_1374_; uint8_t v_allowNonModules_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_buildType_1360_ = lean_ctor_get_uint8(v_cfg_1359_, sizeof(void*)*13);
v_leanOptions_1361_ = lean_ctor_get(v_cfg_1359_, 0);
v_moreLeanArgs_1362_ = lean_ctor_get(v_cfg_1359_, 1);
v_weakLeanArgs_1363_ = lean_ctor_get(v_cfg_1359_, 2);
v_moreServerOptions_1364_ = lean_ctor_get(v_cfg_1359_, 4);
v_weakLeancArgs_1365_ = lean_ctor_get(v_cfg_1359_, 5);
v_moreLinkObjs_1366_ = lean_ctor_get(v_cfg_1359_, 6);
v_moreLinkLibs_1367_ = lean_ctor_get(v_cfg_1359_, 7);
v_moreLinkArgs_1368_ = lean_ctor_get(v_cfg_1359_, 8);
v_weakLinkArgs_1369_ = lean_ctor_get(v_cfg_1359_, 9);
v_backend_1370_ = lean_ctor_get_uint8(v_cfg_1359_, sizeof(void*)*13 + 1);
v_platformIndependent_1371_ = lean_ctor_get(v_cfg_1359_, 10);
v_dynlibs_1372_ = lean_ctor_get(v_cfg_1359_, 11);
v_plugins_1373_ = lean_ctor_get(v_cfg_1359_, 12);
v_requiresModuleSystem_1374_ = lean_ctor_get_uint8(v_cfg_1359_, sizeof(void*)*13 + 2);
v_allowNonModules_1375_ = lean_ctor_get_uint8(v_cfg_1359_, sizeof(void*)*13 + 3);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_cfg_1359_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; 
v_unused_1383_ = lean_ctor_get(v_cfg_1359_, 3);
lean_dec(v_unused_1383_);
v___x_1377_ = v_cfg_1359_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_plugins_1373_);
lean_inc(v_dynlibs_1372_);
lean_inc(v_platformIndependent_1371_);
lean_inc(v_weakLinkArgs_1369_);
lean_inc(v_moreLinkArgs_1368_);
lean_inc(v_moreLinkLibs_1367_);
lean_inc(v_moreLinkObjs_1366_);
lean_inc(v_weakLeancArgs_1365_);
lean_inc(v_moreServerOptions_1364_);
lean_inc(v_weakLeanArgs_1363_);
lean_inc(v_moreLeanArgs_1362_);
lean_inc(v_leanOptions_1361_);
lean_dec(v_cfg_1359_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 3, v_val_1358_);
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_leanOptions_1361_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_moreLeanArgs_1362_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_weakLeanArgs_1363_);
lean_ctor_set(v_reuseFailAlloc_1381_, 3, v_val_1358_);
lean_ctor_set(v_reuseFailAlloc_1381_, 4, v_moreServerOptions_1364_);
lean_ctor_set(v_reuseFailAlloc_1381_, 5, v_weakLeancArgs_1365_);
lean_ctor_set(v_reuseFailAlloc_1381_, 6, v_moreLinkObjs_1366_);
lean_ctor_set(v_reuseFailAlloc_1381_, 7, v_moreLinkLibs_1367_);
lean_ctor_set(v_reuseFailAlloc_1381_, 8, v_moreLinkArgs_1368_);
lean_ctor_set(v_reuseFailAlloc_1381_, 9, v_weakLinkArgs_1369_);
lean_ctor_set(v_reuseFailAlloc_1381_, 10, v_platformIndependent_1371_);
lean_ctor_set(v_reuseFailAlloc_1381_, 11, v_dynlibs_1372_);
lean_ctor_set(v_reuseFailAlloc_1381_, 12, v_plugins_1373_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*13, v_buildType_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*13 + 1, v_backend_1370_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1374_);
lean_ctor_set_uint8(v_reuseFailAlloc_1381_, sizeof(void*)*13 + 3, v_allowNonModules_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1384_, lean_object* v_cfg_1385_){
_start:
{
uint8_t v_buildType_1386_; lean_object* v_leanOptions_1387_; lean_object* v_moreLeanArgs_1388_; lean_object* v_weakLeanArgs_1389_; lean_object* v_moreLeancArgs_1390_; lean_object* v_moreServerOptions_1391_; lean_object* v_weakLeancArgs_1392_; lean_object* v_moreLinkObjs_1393_; lean_object* v_moreLinkLibs_1394_; lean_object* v_moreLinkArgs_1395_; lean_object* v_weakLinkArgs_1396_; uint8_t v_backend_1397_; lean_object* v_platformIndependent_1398_; lean_object* v_dynlibs_1399_; lean_object* v_plugins_1400_; uint8_t v_requiresModuleSystem_1401_; uint8_t v_allowNonModules_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1410_; 
v_buildType_1386_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13);
v_leanOptions_1387_ = lean_ctor_get(v_cfg_1385_, 0);
v_moreLeanArgs_1388_ = lean_ctor_get(v_cfg_1385_, 1);
v_weakLeanArgs_1389_ = lean_ctor_get(v_cfg_1385_, 2);
v_moreLeancArgs_1390_ = lean_ctor_get(v_cfg_1385_, 3);
v_moreServerOptions_1391_ = lean_ctor_get(v_cfg_1385_, 4);
v_weakLeancArgs_1392_ = lean_ctor_get(v_cfg_1385_, 5);
v_moreLinkObjs_1393_ = lean_ctor_get(v_cfg_1385_, 6);
v_moreLinkLibs_1394_ = lean_ctor_get(v_cfg_1385_, 7);
v_moreLinkArgs_1395_ = lean_ctor_get(v_cfg_1385_, 8);
v_weakLinkArgs_1396_ = lean_ctor_get(v_cfg_1385_, 9);
v_backend_1397_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13 + 1);
v_platformIndependent_1398_ = lean_ctor_get(v_cfg_1385_, 10);
v_dynlibs_1399_ = lean_ctor_get(v_cfg_1385_, 11);
v_plugins_1400_ = lean_ctor_get(v_cfg_1385_, 12);
v_requiresModuleSystem_1401_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13 + 2);
v_allowNonModules_1402_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13 + 3);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_cfg_1385_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1404_ = v_cfg_1385_;
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_plugins_1400_);
lean_inc(v_dynlibs_1399_);
lean_inc(v_platformIndependent_1398_);
lean_inc(v_weakLinkArgs_1396_);
lean_inc(v_moreLinkArgs_1395_);
lean_inc(v_moreLinkLibs_1394_);
lean_inc(v_moreLinkObjs_1393_);
lean_inc(v_weakLeancArgs_1392_);
lean_inc(v_moreServerOptions_1391_);
lean_inc(v_moreLeancArgs_1390_);
lean_inc(v_weakLeanArgs_1389_);
lean_inc(v_moreLeanArgs_1388_);
lean_inc(v_leanOptions_1387_);
lean_dec(v_cfg_1385_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1410_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_apply_1(v_f_1384_, v_moreLeancArgs_1390_);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 3, v___x_1406_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_leanOptions_1387_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_moreLeanArgs_1388_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_weakLeanArgs_1389_);
lean_ctor_set(v_reuseFailAlloc_1409_, 3, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1409_, 4, v_moreServerOptions_1391_);
lean_ctor_set(v_reuseFailAlloc_1409_, 5, v_weakLeancArgs_1392_);
lean_ctor_set(v_reuseFailAlloc_1409_, 6, v_moreLinkObjs_1393_);
lean_ctor_set(v_reuseFailAlloc_1409_, 7, v_moreLinkLibs_1394_);
lean_ctor_set(v_reuseFailAlloc_1409_, 8, v_moreLinkArgs_1395_);
lean_ctor_set(v_reuseFailAlloc_1409_, 9, v_weakLinkArgs_1396_);
lean_ctor_set(v_reuseFailAlloc_1409_, 10, v_platformIndependent_1398_);
lean_ctor_set(v_reuseFailAlloc_1409_, 11, v_dynlibs_1399_);
lean_ctor_set(v_reuseFailAlloc_1409_, 12, v_plugins_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1409_, sizeof(void*)*13, v_buildType_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1409_, sizeof(void*)*13 + 1, v_backend_1397_);
lean_ctor_set_uint8(v_reuseFailAlloc_1409_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1409_, sizeof(void*)*13 + 3, v_allowNonModules_1402_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1421_){
_start:
{
lean_object* v_moreServerOptions_1422_; 
v_moreServerOptions_1422_ = lean_ctor_get(v_cfg_1421_, 4);
lean_inc_ref(v_moreServerOptions_1422_);
return v_moreServerOptions_1422_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1423_);
lean_dec_ref(v_cfg_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1425_, lean_object* v_cfg_1426_){
_start:
{
uint8_t v_buildType_1427_; lean_object* v_leanOptions_1428_; lean_object* v_moreLeanArgs_1429_; lean_object* v_weakLeanArgs_1430_; lean_object* v_moreLeancArgs_1431_; lean_object* v_weakLeancArgs_1432_; lean_object* v_moreLinkObjs_1433_; lean_object* v_moreLinkLibs_1434_; lean_object* v_moreLinkArgs_1435_; lean_object* v_weakLinkArgs_1436_; uint8_t v_backend_1437_; lean_object* v_platformIndependent_1438_; lean_object* v_dynlibs_1439_; lean_object* v_plugins_1440_; uint8_t v_requiresModuleSystem_1441_; uint8_t v_allowNonModules_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
v_buildType_1427_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*13);
v_leanOptions_1428_ = lean_ctor_get(v_cfg_1426_, 0);
v_moreLeanArgs_1429_ = lean_ctor_get(v_cfg_1426_, 1);
v_weakLeanArgs_1430_ = lean_ctor_get(v_cfg_1426_, 2);
v_moreLeancArgs_1431_ = lean_ctor_get(v_cfg_1426_, 3);
v_weakLeancArgs_1432_ = lean_ctor_get(v_cfg_1426_, 5);
v_moreLinkObjs_1433_ = lean_ctor_get(v_cfg_1426_, 6);
v_moreLinkLibs_1434_ = lean_ctor_get(v_cfg_1426_, 7);
v_moreLinkArgs_1435_ = lean_ctor_get(v_cfg_1426_, 8);
v_weakLinkArgs_1436_ = lean_ctor_get(v_cfg_1426_, 9);
v_backend_1437_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*13 + 1);
v_platformIndependent_1438_ = lean_ctor_get(v_cfg_1426_, 10);
v_dynlibs_1439_ = lean_ctor_get(v_cfg_1426_, 11);
v_plugins_1440_ = lean_ctor_get(v_cfg_1426_, 12);
v_requiresModuleSystem_1441_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*13 + 2);
v_allowNonModules_1442_ = lean_ctor_get_uint8(v_cfg_1426_, sizeof(void*)*13 + 3);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_cfg_1426_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v_cfg_1426_, 4);
lean_dec(v_unused_1450_);
v___x_1444_ = v_cfg_1426_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_plugins_1440_);
lean_inc(v_dynlibs_1439_);
lean_inc(v_platformIndependent_1438_);
lean_inc(v_weakLinkArgs_1436_);
lean_inc(v_moreLinkArgs_1435_);
lean_inc(v_moreLinkLibs_1434_);
lean_inc(v_moreLinkObjs_1433_);
lean_inc(v_weakLeancArgs_1432_);
lean_inc(v_moreLeancArgs_1431_);
lean_inc(v_weakLeanArgs_1430_);
lean_inc(v_moreLeanArgs_1429_);
lean_inc(v_leanOptions_1428_);
lean_dec(v_cfg_1426_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 4, v_val_1425_);
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_leanOptions_1428_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_moreLeanArgs_1429_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_weakLeanArgs_1430_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_moreLeancArgs_1431_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v_val_1425_);
lean_ctor_set(v_reuseFailAlloc_1448_, 5, v_weakLeancArgs_1432_);
lean_ctor_set(v_reuseFailAlloc_1448_, 6, v_moreLinkObjs_1433_);
lean_ctor_set(v_reuseFailAlloc_1448_, 7, v_moreLinkLibs_1434_);
lean_ctor_set(v_reuseFailAlloc_1448_, 8, v_moreLinkArgs_1435_);
lean_ctor_set(v_reuseFailAlloc_1448_, 9, v_weakLinkArgs_1436_);
lean_ctor_set(v_reuseFailAlloc_1448_, 10, v_platformIndependent_1438_);
lean_ctor_set(v_reuseFailAlloc_1448_, 11, v_dynlibs_1439_);
lean_ctor_set(v_reuseFailAlloc_1448_, 12, v_plugins_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*13, v_buildType_1427_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*13 + 1, v_backend_1437_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1441_);
lean_ctor_set_uint8(v_reuseFailAlloc_1448_, sizeof(void*)*13 + 3, v_allowNonModules_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1451_, lean_object* v_cfg_1452_){
_start:
{
uint8_t v_buildType_1453_; lean_object* v_leanOptions_1454_; lean_object* v_moreLeanArgs_1455_; lean_object* v_weakLeanArgs_1456_; lean_object* v_moreLeancArgs_1457_; lean_object* v_moreServerOptions_1458_; lean_object* v_weakLeancArgs_1459_; lean_object* v_moreLinkObjs_1460_; lean_object* v_moreLinkLibs_1461_; lean_object* v_moreLinkArgs_1462_; lean_object* v_weakLinkArgs_1463_; uint8_t v_backend_1464_; lean_object* v_platformIndependent_1465_; lean_object* v_dynlibs_1466_; lean_object* v_plugins_1467_; uint8_t v_requiresModuleSystem_1468_; uint8_t v_allowNonModules_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1477_; 
v_buildType_1453_ = lean_ctor_get_uint8(v_cfg_1452_, sizeof(void*)*13);
v_leanOptions_1454_ = lean_ctor_get(v_cfg_1452_, 0);
v_moreLeanArgs_1455_ = lean_ctor_get(v_cfg_1452_, 1);
v_weakLeanArgs_1456_ = lean_ctor_get(v_cfg_1452_, 2);
v_moreLeancArgs_1457_ = lean_ctor_get(v_cfg_1452_, 3);
v_moreServerOptions_1458_ = lean_ctor_get(v_cfg_1452_, 4);
v_weakLeancArgs_1459_ = lean_ctor_get(v_cfg_1452_, 5);
v_moreLinkObjs_1460_ = lean_ctor_get(v_cfg_1452_, 6);
v_moreLinkLibs_1461_ = lean_ctor_get(v_cfg_1452_, 7);
v_moreLinkArgs_1462_ = lean_ctor_get(v_cfg_1452_, 8);
v_weakLinkArgs_1463_ = lean_ctor_get(v_cfg_1452_, 9);
v_backend_1464_ = lean_ctor_get_uint8(v_cfg_1452_, sizeof(void*)*13 + 1);
v_platformIndependent_1465_ = lean_ctor_get(v_cfg_1452_, 10);
v_dynlibs_1466_ = lean_ctor_get(v_cfg_1452_, 11);
v_plugins_1467_ = lean_ctor_get(v_cfg_1452_, 12);
v_requiresModuleSystem_1468_ = lean_ctor_get_uint8(v_cfg_1452_, sizeof(void*)*13 + 2);
v_allowNonModules_1469_ = lean_ctor_get_uint8(v_cfg_1452_, sizeof(void*)*13 + 3);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_cfg_1452_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1471_ = v_cfg_1452_;
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_plugins_1467_);
lean_inc(v_dynlibs_1466_);
lean_inc(v_platformIndependent_1465_);
lean_inc(v_weakLinkArgs_1463_);
lean_inc(v_moreLinkArgs_1462_);
lean_inc(v_moreLinkLibs_1461_);
lean_inc(v_moreLinkObjs_1460_);
lean_inc(v_weakLeancArgs_1459_);
lean_inc(v_moreServerOptions_1458_);
lean_inc(v_moreLeancArgs_1457_);
lean_inc(v_weakLeanArgs_1456_);
lean_inc(v_moreLeanArgs_1455_);
lean_inc(v_leanOptions_1454_);
lean_dec(v_cfg_1452_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1477_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1473_ = lean_apply_1(v_f_1451_, v_moreServerOptions_1458_);
if (v_isShared_1472_ == 0)
{
lean_ctor_set(v___x_1471_, 4, v___x_1473_);
v___x_1475_ = v___x_1471_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_leanOptions_1454_);
lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_moreLeanArgs_1455_);
lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_weakLeanArgs_1456_);
lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_moreLeancArgs_1457_);
lean_ctor_set(v_reuseFailAlloc_1476_, 4, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1476_, 5, v_weakLeancArgs_1459_);
lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_moreLinkObjs_1460_);
lean_ctor_set(v_reuseFailAlloc_1476_, 7, v_moreLinkLibs_1461_);
lean_ctor_set(v_reuseFailAlloc_1476_, 8, v_moreLinkArgs_1462_);
lean_ctor_set(v_reuseFailAlloc_1476_, 9, v_weakLinkArgs_1463_);
lean_ctor_set(v_reuseFailAlloc_1476_, 10, v_platformIndependent_1465_);
lean_ctor_set(v_reuseFailAlloc_1476_, 11, v_dynlibs_1466_);
lean_ctor_set(v_reuseFailAlloc_1476_, 12, v_plugins_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13, v_buildType_1453_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 1, v_backend_1464_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1468_);
lean_ctor_set_uint8(v_reuseFailAlloc_1476_, sizeof(void*)*13 + 3, v_allowNonModules_1469_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1488_){
_start:
{
lean_object* v_weakLeancArgs_1489_; 
v_weakLeancArgs_1489_ = lean_ctor_get(v_cfg_1488_, 5);
lean_inc_ref(v_weakLeancArgs_1489_);
return v_weakLeancArgs_1489_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1490_);
lean_dec_ref(v_cfg_1490_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1492_, lean_object* v_cfg_1493_){
_start:
{
uint8_t v_buildType_1494_; lean_object* v_leanOptions_1495_; lean_object* v_moreLeanArgs_1496_; lean_object* v_weakLeanArgs_1497_; lean_object* v_moreLeancArgs_1498_; lean_object* v_moreServerOptions_1499_; lean_object* v_moreLinkObjs_1500_; lean_object* v_moreLinkLibs_1501_; lean_object* v_moreLinkArgs_1502_; lean_object* v_weakLinkArgs_1503_; uint8_t v_backend_1504_; lean_object* v_platformIndependent_1505_; lean_object* v_dynlibs_1506_; lean_object* v_plugins_1507_; uint8_t v_requiresModuleSystem_1508_; uint8_t v_allowNonModules_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_buildType_1494_ = lean_ctor_get_uint8(v_cfg_1493_, sizeof(void*)*13);
v_leanOptions_1495_ = lean_ctor_get(v_cfg_1493_, 0);
v_moreLeanArgs_1496_ = lean_ctor_get(v_cfg_1493_, 1);
v_weakLeanArgs_1497_ = lean_ctor_get(v_cfg_1493_, 2);
v_moreLeancArgs_1498_ = lean_ctor_get(v_cfg_1493_, 3);
v_moreServerOptions_1499_ = lean_ctor_get(v_cfg_1493_, 4);
v_moreLinkObjs_1500_ = lean_ctor_get(v_cfg_1493_, 6);
v_moreLinkLibs_1501_ = lean_ctor_get(v_cfg_1493_, 7);
v_moreLinkArgs_1502_ = lean_ctor_get(v_cfg_1493_, 8);
v_weakLinkArgs_1503_ = lean_ctor_get(v_cfg_1493_, 9);
v_backend_1504_ = lean_ctor_get_uint8(v_cfg_1493_, sizeof(void*)*13 + 1);
v_platformIndependent_1505_ = lean_ctor_get(v_cfg_1493_, 10);
v_dynlibs_1506_ = lean_ctor_get(v_cfg_1493_, 11);
v_plugins_1507_ = lean_ctor_get(v_cfg_1493_, 12);
v_requiresModuleSystem_1508_ = lean_ctor_get_uint8(v_cfg_1493_, sizeof(void*)*13 + 2);
v_allowNonModules_1509_ = lean_ctor_get_uint8(v_cfg_1493_, sizeof(void*)*13 + 3);
v_isSharedCheck_1516_ = !lean_is_exclusive(v_cfg_1493_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v_cfg_1493_, 5);
lean_dec(v_unused_1517_);
v___x_1511_ = v_cfg_1493_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_plugins_1507_);
lean_inc(v_dynlibs_1506_);
lean_inc(v_platformIndependent_1505_);
lean_inc(v_weakLinkArgs_1503_);
lean_inc(v_moreLinkArgs_1502_);
lean_inc(v_moreLinkLibs_1501_);
lean_inc(v_moreLinkObjs_1500_);
lean_inc(v_moreServerOptions_1499_);
lean_inc(v_moreLeancArgs_1498_);
lean_inc(v_weakLeanArgs_1497_);
lean_inc(v_moreLeanArgs_1496_);
lean_inc(v_leanOptions_1495_);
lean_dec(v_cfg_1493_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 5, v_val_1492_);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_leanOptions_1495_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_moreLeanArgs_1496_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_weakLeanArgs_1497_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_moreLeancArgs_1498_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_moreServerOptions_1499_);
lean_ctor_set(v_reuseFailAlloc_1515_, 5, v_val_1492_);
lean_ctor_set(v_reuseFailAlloc_1515_, 6, v_moreLinkObjs_1500_);
lean_ctor_set(v_reuseFailAlloc_1515_, 7, v_moreLinkLibs_1501_);
lean_ctor_set(v_reuseFailAlloc_1515_, 8, v_moreLinkArgs_1502_);
lean_ctor_set(v_reuseFailAlloc_1515_, 9, v_weakLinkArgs_1503_);
lean_ctor_set(v_reuseFailAlloc_1515_, 10, v_platformIndependent_1505_);
lean_ctor_set(v_reuseFailAlloc_1515_, 11, v_dynlibs_1506_);
lean_ctor_set(v_reuseFailAlloc_1515_, 12, v_plugins_1507_);
lean_ctor_set_uint8(v_reuseFailAlloc_1515_, sizeof(void*)*13, v_buildType_1494_);
lean_ctor_set_uint8(v_reuseFailAlloc_1515_, sizeof(void*)*13 + 1, v_backend_1504_);
lean_ctor_set_uint8(v_reuseFailAlloc_1515_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1508_);
lean_ctor_set_uint8(v_reuseFailAlloc_1515_, sizeof(void*)*13 + 3, v_allowNonModules_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1518_, lean_object* v_cfg_1519_){
_start:
{
uint8_t v_buildType_1520_; lean_object* v_leanOptions_1521_; lean_object* v_moreLeanArgs_1522_; lean_object* v_weakLeanArgs_1523_; lean_object* v_moreLeancArgs_1524_; lean_object* v_moreServerOptions_1525_; lean_object* v_weakLeancArgs_1526_; lean_object* v_moreLinkObjs_1527_; lean_object* v_moreLinkLibs_1528_; lean_object* v_moreLinkArgs_1529_; lean_object* v_weakLinkArgs_1530_; uint8_t v_backend_1531_; lean_object* v_platformIndependent_1532_; lean_object* v_dynlibs_1533_; lean_object* v_plugins_1534_; uint8_t v_requiresModuleSystem_1535_; uint8_t v_allowNonModules_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1544_; 
v_buildType_1520_ = lean_ctor_get_uint8(v_cfg_1519_, sizeof(void*)*13);
v_leanOptions_1521_ = lean_ctor_get(v_cfg_1519_, 0);
v_moreLeanArgs_1522_ = lean_ctor_get(v_cfg_1519_, 1);
v_weakLeanArgs_1523_ = lean_ctor_get(v_cfg_1519_, 2);
v_moreLeancArgs_1524_ = lean_ctor_get(v_cfg_1519_, 3);
v_moreServerOptions_1525_ = lean_ctor_get(v_cfg_1519_, 4);
v_weakLeancArgs_1526_ = lean_ctor_get(v_cfg_1519_, 5);
v_moreLinkObjs_1527_ = lean_ctor_get(v_cfg_1519_, 6);
v_moreLinkLibs_1528_ = lean_ctor_get(v_cfg_1519_, 7);
v_moreLinkArgs_1529_ = lean_ctor_get(v_cfg_1519_, 8);
v_weakLinkArgs_1530_ = lean_ctor_get(v_cfg_1519_, 9);
v_backend_1531_ = lean_ctor_get_uint8(v_cfg_1519_, sizeof(void*)*13 + 1);
v_platformIndependent_1532_ = lean_ctor_get(v_cfg_1519_, 10);
v_dynlibs_1533_ = lean_ctor_get(v_cfg_1519_, 11);
v_plugins_1534_ = lean_ctor_get(v_cfg_1519_, 12);
v_requiresModuleSystem_1535_ = lean_ctor_get_uint8(v_cfg_1519_, sizeof(void*)*13 + 2);
v_allowNonModules_1536_ = lean_ctor_get_uint8(v_cfg_1519_, sizeof(void*)*13 + 3);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_cfg_1519_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1538_ = v_cfg_1519_;
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_plugins_1534_);
lean_inc(v_dynlibs_1533_);
lean_inc(v_platformIndependent_1532_);
lean_inc(v_weakLinkArgs_1530_);
lean_inc(v_moreLinkArgs_1529_);
lean_inc(v_moreLinkLibs_1528_);
lean_inc(v_moreLinkObjs_1527_);
lean_inc(v_weakLeancArgs_1526_);
lean_inc(v_moreServerOptions_1525_);
lean_inc(v_moreLeancArgs_1524_);
lean_inc(v_weakLeanArgs_1523_);
lean_inc(v_moreLeanArgs_1522_);
lean_inc(v_leanOptions_1521_);
lean_dec(v_cfg_1519_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1544_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1542_; 
v___x_1540_ = lean_apply_1(v_f_1518_, v_weakLeancArgs_1526_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 5, v___x_1540_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_leanOptions_1521_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_moreLeanArgs_1522_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_weakLeanArgs_1523_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_moreLeancArgs_1524_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_moreServerOptions_1525_);
lean_ctor_set(v_reuseFailAlloc_1543_, 5, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1543_, 6, v_moreLinkObjs_1527_);
lean_ctor_set(v_reuseFailAlloc_1543_, 7, v_moreLinkLibs_1528_);
lean_ctor_set(v_reuseFailAlloc_1543_, 8, v_moreLinkArgs_1529_);
lean_ctor_set(v_reuseFailAlloc_1543_, 9, v_weakLinkArgs_1530_);
lean_ctor_set(v_reuseFailAlloc_1543_, 10, v_platformIndependent_1532_);
lean_ctor_set(v_reuseFailAlloc_1543_, 11, v_dynlibs_1533_);
lean_ctor_set(v_reuseFailAlloc_1543_, 12, v_plugins_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1543_, sizeof(void*)*13, v_buildType_1520_);
lean_ctor_set_uint8(v_reuseFailAlloc_1543_, sizeof(void*)*13 + 1, v_backend_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1543_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1535_);
lean_ctor_set_uint8(v_reuseFailAlloc_1543_, sizeof(void*)*13 + 3, v_allowNonModules_1536_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1555_){
_start:
{
lean_object* v_moreLinkObjs_1556_; 
v_moreLinkObjs_1556_ = lean_ctor_get(v_cfg_1555_, 6);
lean_inc_ref(v_moreLinkObjs_1556_);
return v_moreLinkObjs_1556_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1557_);
lean_dec_ref(v_cfg_1557_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1559_, lean_object* v_cfg_1560_){
_start:
{
uint8_t v_buildType_1561_; lean_object* v_leanOptions_1562_; lean_object* v_moreLeanArgs_1563_; lean_object* v_weakLeanArgs_1564_; lean_object* v_moreLeancArgs_1565_; lean_object* v_moreServerOptions_1566_; lean_object* v_weakLeancArgs_1567_; lean_object* v_moreLinkLibs_1568_; lean_object* v_moreLinkArgs_1569_; lean_object* v_weakLinkArgs_1570_; uint8_t v_backend_1571_; lean_object* v_platformIndependent_1572_; lean_object* v_dynlibs_1573_; lean_object* v_plugins_1574_; uint8_t v_requiresModuleSystem_1575_; uint8_t v_allowNonModules_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_buildType_1561_ = lean_ctor_get_uint8(v_cfg_1560_, sizeof(void*)*13);
v_leanOptions_1562_ = lean_ctor_get(v_cfg_1560_, 0);
v_moreLeanArgs_1563_ = lean_ctor_get(v_cfg_1560_, 1);
v_weakLeanArgs_1564_ = lean_ctor_get(v_cfg_1560_, 2);
v_moreLeancArgs_1565_ = lean_ctor_get(v_cfg_1560_, 3);
v_moreServerOptions_1566_ = lean_ctor_get(v_cfg_1560_, 4);
v_weakLeancArgs_1567_ = lean_ctor_get(v_cfg_1560_, 5);
v_moreLinkLibs_1568_ = lean_ctor_get(v_cfg_1560_, 7);
v_moreLinkArgs_1569_ = lean_ctor_get(v_cfg_1560_, 8);
v_weakLinkArgs_1570_ = lean_ctor_get(v_cfg_1560_, 9);
v_backend_1571_ = lean_ctor_get_uint8(v_cfg_1560_, sizeof(void*)*13 + 1);
v_platformIndependent_1572_ = lean_ctor_get(v_cfg_1560_, 10);
v_dynlibs_1573_ = lean_ctor_get(v_cfg_1560_, 11);
v_plugins_1574_ = lean_ctor_get(v_cfg_1560_, 12);
v_requiresModuleSystem_1575_ = lean_ctor_get_uint8(v_cfg_1560_, sizeof(void*)*13 + 2);
v_allowNonModules_1576_ = lean_ctor_get_uint8(v_cfg_1560_, sizeof(void*)*13 + 3);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_cfg_1560_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_cfg_1560_, 6);
lean_dec(v_unused_1584_);
v___x_1578_ = v_cfg_1560_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_plugins_1574_);
lean_inc(v_dynlibs_1573_);
lean_inc(v_platformIndependent_1572_);
lean_inc(v_weakLinkArgs_1570_);
lean_inc(v_moreLinkArgs_1569_);
lean_inc(v_moreLinkLibs_1568_);
lean_inc(v_weakLeancArgs_1567_);
lean_inc(v_moreServerOptions_1566_);
lean_inc(v_moreLeancArgs_1565_);
lean_inc(v_weakLeanArgs_1564_);
lean_inc(v_moreLeanArgs_1563_);
lean_inc(v_leanOptions_1562_);
lean_dec(v_cfg_1560_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 6, v_val_1559_);
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_leanOptions_1562_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_moreLeanArgs_1563_);
lean_ctor_set(v_reuseFailAlloc_1582_, 2, v_weakLeanArgs_1564_);
lean_ctor_set(v_reuseFailAlloc_1582_, 3, v_moreLeancArgs_1565_);
lean_ctor_set(v_reuseFailAlloc_1582_, 4, v_moreServerOptions_1566_);
lean_ctor_set(v_reuseFailAlloc_1582_, 5, v_weakLeancArgs_1567_);
lean_ctor_set(v_reuseFailAlloc_1582_, 6, v_val_1559_);
lean_ctor_set(v_reuseFailAlloc_1582_, 7, v_moreLinkLibs_1568_);
lean_ctor_set(v_reuseFailAlloc_1582_, 8, v_moreLinkArgs_1569_);
lean_ctor_set(v_reuseFailAlloc_1582_, 9, v_weakLinkArgs_1570_);
lean_ctor_set(v_reuseFailAlloc_1582_, 10, v_platformIndependent_1572_);
lean_ctor_set(v_reuseFailAlloc_1582_, 11, v_dynlibs_1573_);
lean_ctor_set(v_reuseFailAlloc_1582_, 12, v_plugins_1574_);
lean_ctor_set_uint8(v_reuseFailAlloc_1582_, sizeof(void*)*13, v_buildType_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1582_, sizeof(void*)*13 + 1, v_backend_1571_);
lean_ctor_set_uint8(v_reuseFailAlloc_1582_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1575_);
lean_ctor_set_uint8(v_reuseFailAlloc_1582_, sizeof(void*)*13 + 3, v_allowNonModules_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1585_, lean_object* v_cfg_1586_){
_start:
{
uint8_t v_buildType_1587_; lean_object* v_leanOptions_1588_; lean_object* v_moreLeanArgs_1589_; lean_object* v_weakLeanArgs_1590_; lean_object* v_moreLeancArgs_1591_; lean_object* v_moreServerOptions_1592_; lean_object* v_weakLeancArgs_1593_; lean_object* v_moreLinkObjs_1594_; lean_object* v_moreLinkLibs_1595_; lean_object* v_moreLinkArgs_1596_; lean_object* v_weakLinkArgs_1597_; uint8_t v_backend_1598_; lean_object* v_platformIndependent_1599_; lean_object* v_dynlibs_1600_; lean_object* v_plugins_1601_; uint8_t v_requiresModuleSystem_1602_; uint8_t v_allowNonModules_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1611_; 
v_buildType_1587_ = lean_ctor_get_uint8(v_cfg_1586_, sizeof(void*)*13);
v_leanOptions_1588_ = lean_ctor_get(v_cfg_1586_, 0);
v_moreLeanArgs_1589_ = lean_ctor_get(v_cfg_1586_, 1);
v_weakLeanArgs_1590_ = lean_ctor_get(v_cfg_1586_, 2);
v_moreLeancArgs_1591_ = lean_ctor_get(v_cfg_1586_, 3);
v_moreServerOptions_1592_ = lean_ctor_get(v_cfg_1586_, 4);
v_weakLeancArgs_1593_ = lean_ctor_get(v_cfg_1586_, 5);
v_moreLinkObjs_1594_ = lean_ctor_get(v_cfg_1586_, 6);
v_moreLinkLibs_1595_ = lean_ctor_get(v_cfg_1586_, 7);
v_moreLinkArgs_1596_ = lean_ctor_get(v_cfg_1586_, 8);
v_weakLinkArgs_1597_ = lean_ctor_get(v_cfg_1586_, 9);
v_backend_1598_ = lean_ctor_get_uint8(v_cfg_1586_, sizeof(void*)*13 + 1);
v_platformIndependent_1599_ = lean_ctor_get(v_cfg_1586_, 10);
v_dynlibs_1600_ = lean_ctor_get(v_cfg_1586_, 11);
v_plugins_1601_ = lean_ctor_get(v_cfg_1586_, 12);
v_requiresModuleSystem_1602_ = lean_ctor_get_uint8(v_cfg_1586_, sizeof(void*)*13 + 2);
v_allowNonModules_1603_ = lean_ctor_get_uint8(v_cfg_1586_, sizeof(void*)*13 + 3);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_cfg_1586_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1605_ = v_cfg_1586_;
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_plugins_1601_);
lean_inc(v_dynlibs_1600_);
lean_inc(v_platformIndependent_1599_);
lean_inc(v_weakLinkArgs_1597_);
lean_inc(v_moreLinkArgs_1596_);
lean_inc(v_moreLinkLibs_1595_);
lean_inc(v_moreLinkObjs_1594_);
lean_inc(v_weakLeancArgs_1593_);
lean_inc(v_moreServerOptions_1592_);
lean_inc(v_moreLeancArgs_1591_);
lean_inc(v_weakLeanArgs_1590_);
lean_inc(v_moreLeanArgs_1589_);
lean_inc(v_leanOptions_1588_);
lean_dec(v_cfg_1586_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1611_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_apply_1(v_f_1585_, v_moreLinkObjs_1594_);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 6, v___x_1607_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_leanOptions_1588_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_moreLeanArgs_1589_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_weakLeanArgs_1590_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_moreLeancArgs_1591_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_moreServerOptions_1592_);
lean_ctor_set(v_reuseFailAlloc_1610_, 5, v_weakLeancArgs_1593_);
lean_ctor_set(v_reuseFailAlloc_1610_, 6, v___x_1607_);
lean_ctor_set(v_reuseFailAlloc_1610_, 7, v_moreLinkLibs_1595_);
lean_ctor_set(v_reuseFailAlloc_1610_, 8, v_moreLinkArgs_1596_);
lean_ctor_set(v_reuseFailAlloc_1610_, 9, v_weakLinkArgs_1597_);
lean_ctor_set(v_reuseFailAlloc_1610_, 10, v_platformIndependent_1599_);
lean_ctor_set(v_reuseFailAlloc_1610_, 11, v_dynlibs_1600_);
lean_ctor_set(v_reuseFailAlloc_1610_, 12, v_plugins_1601_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13, v_buildType_1587_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13 + 1, v_backend_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13 + 3, v_allowNonModules_1603_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1616_);
lean_dec_ref(v_x_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1629_){
_start:
{
lean_object* v_moreLinkLibs_1630_; 
v_moreLinkLibs_1630_ = lean_ctor_get(v_cfg_1629_, 7);
lean_inc_ref(v_moreLinkLibs_1630_);
return v_moreLinkLibs_1630_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1631_);
lean_dec_ref(v_cfg_1631_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1633_, lean_object* v_cfg_1634_){
_start:
{
uint8_t v_buildType_1635_; lean_object* v_leanOptions_1636_; lean_object* v_moreLeanArgs_1637_; lean_object* v_weakLeanArgs_1638_; lean_object* v_moreLeancArgs_1639_; lean_object* v_moreServerOptions_1640_; lean_object* v_weakLeancArgs_1641_; lean_object* v_moreLinkObjs_1642_; lean_object* v_moreLinkArgs_1643_; lean_object* v_weakLinkArgs_1644_; uint8_t v_backend_1645_; lean_object* v_platformIndependent_1646_; lean_object* v_dynlibs_1647_; lean_object* v_plugins_1648_; uint8_t v_requiresModuleSystem_1649_; uint8_t v_allowNonModules_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_buildType_1635_ = lean_ctor_get_uint8(v_cfg_1634_, sizeof(void*)*13);
v_leanOptions_1636_ = lean_ctor_get(v_cfg_1634_, 0);
v_moreLeanArgs_1637_ = lean_ctor_get(v_cfg_1634_, 1);
v_weakLeanArgs_1638_ = lean_ctor_get(v_cfg_1634_, 2);
v_moreLeancArgs_1639_ = lean_ctor_get(v_cfg_1634_, 3);
v_moreServerOptions_1640_ = lean_ctor_get(v_cfg_1634_, 4);
v_weakLeancArgs_1641_ = lean_ctor_get(v_cfg_1634_, 5);
v_moreLinkObjs_1642_ = lean_ctor_get(v_cfg_1634_, 6);
v_moreLinkArgs_1643_ = lean_ctor_get(v_cfg_1634_, 8);
v_weakLinkArgs_1644_ = lean_ctor_get(v_cfg_1634_, 9);
v_backend_1645_ = lean_ctor_get_uint8(v_cfg_1634_, sizeof(void*)*13 + 1);
v_platformIndependent_1646_ = lean_ctor_get(v_cfg_1634_, 10);
v_dynlibs_1647_ = lean_ctor_get(v_cfg_1634_, 11);
v_plugins_1648_ = lean_ctor_get(v_cfg_1634_, 12);
v_requiresModuleSystem_1649_ = lean_ctor_get_uint8(v_cfg_1634_, sizeof(void*)*13 + 2);
v_allowNonModules_1650_ = lean_ctor_get_uint8(v_cfg_1634_, sizeof(void*)*13 + 3);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_cfg_1634_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_cfg_1634_, 7);
lean_dec(v_unused_1658_);
v___x_1652_ = v_cfg_1634_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_plugins_1648_);
lean_inc(v_dynlibs_1647_);
lean_inc(v_platformIndependent_1646_);
lean_inc(v_weakLinkArgs_1644_);
lean_inc(v_moreLinkArgs_1643_);
lean_inc(v_moreLinkObjs_1642_);
lean_inc(v_weakLeancArgs_1641_);
lean_inc(v_moreServerOptions_1640_);
lean_inc(v_moreLeancArgs_1639_);
lean_inc(v_weakLeanArgs_1638_);
lean_inc(v_moreLeanArgs_1637_);
lean_inc(v_leanOptions_1636_);
lean_dec(v_cfg_1634_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 7, v_val_1633_);
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_leanOptions_1636_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_moreLeanArgs_1637_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_weakLeanArgs_1638_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_moreLeancArgs_1639_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_moreServerOptions_1640_);
lean_ctor_set(v_reuseFailAlloc_1656_, 5, v_weakLeancArgs_1641_);
lean_ctor_set(v_reuseFailAlloc_1656_, 6, v_moreLinkObjs_1642_);
lean_ctor_set(v_reuseFailAlloc_1656_, 7, v_val_1633_);
lean_ctor_set(v_reuseFailAlloc_1656_, 8, v_moreLinkArgs_1643_);
lean_ctor_set(v_reuseFailAlloc_1656_, 9, v_weakLinkArgs_1644_);
lean_ctor_set(v_reuseFailAlloc_1656_, 10, v_platformIndependent_1646_);
lean_ctor_set(v_reuseFailAlloc_1656_, 11, v_dynlibs_1647_);
lean_ctor_set(v_reuseFailAlloc_1656_, 12, v_plugins_1648_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, sizeof(void*)*13, v_buildType_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, sizeof(void*)*13 + 1, v_backend_1645_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1649_);
lean_ctor_set_uint8(v_reuseFailAlloc_1656_, sizeof(void*)*13 + 3, v_allowNonModules_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1659_, lean_object* v_cfg_1660_){
_start:
{
uint8_t v_buildType_1661_; lean_object* v_leanOptions_1662_; lean_object* v_moreLeanArgs_1663_; lean_object* v_weakLeanArgs_1664_; lean_object* v_moreLeancArgs_1665_; lean_object* v_moreServerOptions_1666_; lean_object* v_weakLeancArgs_1667_; lean_object* v_moreLinkObjs_1668_; lean_object* v_moreLinkLibs_1669_; lean_object* v_moreLinkArgs_1670_; lean_object* v_weakLinkArgs_1671_; uint8_t v_backend_1672_; lean_object* v_platformIndependent_1673_; lean_object* v_dynlibs_1674_; lean_object* v_plugins_1675_; uint8_t v_requiresModuleSystem_1676_; uint8_t v_allowNonModules_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1685_; 
v_buildType_1661_ = lean_ctor_get_uint8(v_cfg_1660_, sizeof(void*)*13);
v_leanOptions_1662_ = lean_ctor_get(v_cfg_1660_, 0);
v_moreLeanArgs_1663_ = lean_ctor_get(v_cfg_1660_, 1);
v_weakLeanArgs_1664_ = lean_ctor_get(v_cfg_1660_, 2);
v_moreLeancArgs_1665_ = lean_ctor_get(v_cfg_1660_, 3);
v_moreServerOptions_1666_ = lean_ctor_get(v_cfg_1660_, 4);
v_weakLeancArgs_1667_ = lean_ctor_get(v_cfg_1660_, 5);
v_moreLinkObjs_1668_ = lean_ctor_get(v_cfg_1660_, 6);
v_moreLinkLibs_1669_ = lean_ctor_get(v_cfg_1660_, 7);
v_moreLinkArgs_1670_ = lean_ctor_get(v_cfg_1660_, 8);
v_weakLinkArgs_1671_ = lean_ctor_get(v_cfg_1660_, 9);
v_backend_1672_ = lean_ctor_get_uint8(v_cfg_1660_, sizeof(void*)*13 + 1);
v_platformIndependent_1673_ = lean_ctor_get(v_cfg_1660_, 10);
v_dynlibs_1674_ = lean_ctor_get(v_cfg_1660_, 11);
v_plugins_1675_ = lean_ctor_get(v_cfg_1660_, 12);
v_requiresModuleSystem_1676_ = lean_ctor_get_uint8(v_cfg_1660_, sizeof(void*)*13 + 2);
v_allowNonModules_1677_ = lean_ctor_get_uint8(v_cfg_1660_, sizeof(void*)*13 + 3);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_cfg_1660_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1679_ = v_cfg_1660_;
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_plugins_1675_);
lean_inc(v_dynlibs_1674_);
lean_inc(v_platformIndependent_1673_);
lean_inc(v_weakLinkArgs_1671_);
lean_inc(v_moreLinkArgs_1670_);
lean_inc(v_moreLinkLibs_1669_);
lean_inc(v_moreLinkObjs_1668_);
lean_inc(v_weakLeancArgs_1667_);
lean_inc(v_moreServerOptions_1666_);
lean_inc(v_moreLeancArgs_1665_);
lean_inc(v_weakLeanArgs_1664_);
lean_inc(v_moreLeanArgs_1663_);
lean_inc(v_leanOptions_1662_);
lean_dec(v_cfg_1660_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_apply_1(v_f_1659_, v_moreLinkLibs_1669_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 7, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_leanOptions_1662_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_moreLeanArgs_1663_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_weakLeanArgs_1664_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_moreLeancArgs_1665_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_moreServerOptions_1666_);
lean_ctor_set(v_reuseFailAlloc_1684_, 5, v_weakLeancArgs_1667_);
lean_ctor_set(v_reuseFailAlloc_1684_, 6, v_moreLinkObjs_1668_);
lean_ctor_set(v_reuseFailAlloc_1684_, 7, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1684_, 8, v_moreLinkArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1684_, 9, v_weakLinkArgs_1671_);
lean_ctor_set(v_reuseFailAlloc_1684_, 10, v_platformIndependent_1673_);
lean_ctor_set(v_reuseFailAlloc_1684_, 11, v_dynlibs_1674_);
lean_ctor_set(v_reuseFailAlloc_1684_, 12, v_plugins_1675_);
lean_ctor_set_uint8(v_reuseFailAlloc_1684_, sizeof(void*)*13, v_buildType_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1684_, sizeof(void*)*13 + 1, v_backend_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1684_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1684_, sizeof(void*)*13 + 3, v_allowNonModules_1677_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1696_){
_start:
{
lean_object* v_moreLinkArgs_1697_; 
v_moreLinkArgs_1697_ = lean_ctor_get(v_cfg_1696_, 8);
lean_inc_ref(v_moreLinkArgs_1697_);
return v_moreLinkArgs_1697_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1698_);
lean_dec_ref(v_cfg_1698_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1700_, lean_object* v_cfg_1701_){
_start:
{
uint8_t v_buildType_1702_; lean_object* v_leanOptions_1703_; lean_object* v_moreLeanArgs_1704_; lean_object* v_weakLeanArgs_1705_; lean_object* v_moreLeancArgs_1706_; lean_object* v_moreServerOptions_1707_; lean_object* v_weakLeancArgs_1708_; lean_object* v_moreLinkObjs_1709_; lean_object* v_moreLinkLibs_1710_; lean_object* v_weakLinkArgs_1711_; uint8_t v_backend_1712_; lean_object* v_platformIndependent_1713_; lean_object* v_dynlibs_1714_; lean_object* v_plugins_1715_; uint8_t v_requiresModuleSystem_1716_; uint8_t v_allowNonModules_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_buildType_1702_ = lean_ctor_get_uint8(v_cfg_1701_, sizeof(void*)*13);
v_leanOptions_1703_ = lean_ctor_get(v_cfg_1701_, 0);
v_moreLeanArgs_1704_ = lean_ctor_get(v_cfg_1701_, 1);
v_weakLeanArgs_1705_ = lean_ctor_get(v_cfg_1701_, 2);
v_moreLeancArgs_1706_ = lean_ctor_get(v_cfg_1701_, 3);
v_moreServerOptions_1707_ = lean_ctor_get(v_cfg_1701_, 4);
v_weakLeancArgs_1708_ = lean_ctor_get(v_cfg_1701_, 5);
v_moreLinkObjs_1709_ = lean_ctor_get(v_cfg_1701_, 6);
v_moreLinkLibs_1710_ = lean_ctor_get(v_cfg_1701_, 7);
v_weakLinkArgs_1711_ = lean_ctor_get(v_cfg_1701_, 9);
v_backend_1712_ = lean_ctor_get_uint8(v_cfg_1701_, sizeof(void*)*13 + 1);
v_platformIndependent_1713_ = lean_ctor_get(v_cfg_1701_, 10);
v_dynlibs_1714_ = lean_ctor_get(v_cfg_1701_, 11);
v_plugins_1715_ = lean_ctor_get(v_cfg_1701_, 12);
v_requiresModuleSystem_1716_ = lean_ctor_get_uint8(v_cfg_1701_, sizeof(void*)*13 + 2);
v_allowNonModules_1717_ = lean_ctor_get_uint8(v_cfg_1701_, sizeof(void*)*13 + 3);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_cfg_1701_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v_cfg_1701_, 8);
lean_dec(v_unused_1725_);
v___x_1719_ = v_cfg_1701_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_plugins_1715_);
lean_inc(v_dynlibs_1714_);
lean_inc(v_platformIndependent_1713_);
lean_inc(v_weakLinkArgs_1711_);
lean_inc(v_moreLinkLibs_1710_);
lean_inc(v_moreLinkObjs_1709_);
lean_inc(v_weakLeancArgs_1708_);
lean_inc(v_moreServerOptions_1707_);
lean_inc(v_moreLeancArgs_1706_);
lean_inc(v_weakLeanArgs_1705_);
lean_inc(v_moreLeanArgs_1704_);
lean_inc(v_leanOptions_1703_);
lean_dec(v_cfg_1701_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 8, v_val_1700_);
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_leanOptions_1703_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_moreLeanArgs_1704_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_weakLeanArgs_1705_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_moreLeancArgs_1706_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_moreServerOptions_1707_);
lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_weakLeancArgs_1708_);
lean_ctor_set(v_reuseFailAlloc_1723_, 6, v_moreLinkObjs_1709_);
lean_ctor_set(v_reuseFailAlloc_1723_, 7, v_moreLinkLibs_1710_);
lean_ctor_set(v_reuseFailAlloc_1723_, 8, v_val_1700_);
lean_ctor_set(v_reuseFailAlloc_1723_, 9, v_weakLinkArgs_1711_);
lean_ctor_set(v_reuseFailAlloc_1723_, 10, v_platformIndependent_1713_);
lean_ctor_set(v_reuseFailAlloc_1723_, 11, v_dynlibs_1714_);
lean_ctor_set(v_reuseFailAlloc_1723_, 12, v_plugins_1715_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13, v_buildType_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13 + 1, v_backend_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1716_);
lean_ctor_set_uint8(v_reuseFailAlloc_1723_, sizeof(void*)*13 + 3, v_allowNonModules_1717_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1726_, lean_object* v_cfg_1727_){
_start:
{
uint8_t v_buildType_1728_; lean_object* v_leanOptions_1729_; lean_object* v_moreLeanArgs_1730_; lean_object* v_weakLeanArgs_1731_; lean_object* v_moreLeancArgs_1732_; lean_object* v_moreServerOptions_1733_; lean_object* v_weakLeancArgs_1734_; lean_object* v_moreLinkObjs_1735_; lean_object* v_moreLinkLibs_1736_; lean_object* v_moreLinkArgs_1737_; lean_object* v_weakLinkArgs_1738_; uint8_t v_backend_1739_; lean_object* v_platformIndependent_1740_; lean_object* v_dynlibs_1741_; lean_object* v_plugins_1742_; uint8_t v_requiresModuleSystem_1743_; uint8_t v_allowNonModules_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1752_; 
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
v_dynlibs_1741_ = lean_ctor_get(v_cfg_1727_, 11);
v_plugins_1742_ = lean_ctor_get(v_cfg_1727_, 12);
v_requiresModuleSystem_1743_ = lean_ctor_get_uint8(v_cfg_1727_, sizeof(void*)*13 + 2);
v_allowNonModules_1744_ = lean_ctor_get_uint8(v_cfg_1727_, sizeof(void*)*13 + 3);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_cfg_1727_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1746_ = v_cfg_1727_;
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_plugins_1742_);
lean_inc(v_dynlibs_1741_);
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
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1752_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1748_; lean_object* v___x_1750_; 
v___x_1748_ = lean_apply_1(v_f_1726_, v_moreLinkArgs_1737_);
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 8, v___x_1748_);
v___x_1750_ = v___x_1746_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_leanOptions_1729_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_moreLeanArgs_1730_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_weakLeanArgs_1731_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v_moreLeancArgs_1732_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v_moreServerOptions_1733_);
lean_ctor_set(v_reuseFailAlloc_1751_, 5, v_weakLeancArgs_1734_);
lean_ctor_set(v_reuseFailAlloc_1751_, 6, v_moreLinkObjs_1735_);
lean_ctor_set(v_reuseFailAlloc_1751_, 7, v_moreLinkLibs_1736_);
lean_ctor_set(v_reuseFailAlloc_1751_, 8, v___x_1748_);
lean_ctor_set(v_reuseFailAlloc_1751_, 9, v_weakLinkArgs_1738_);
lean_ctor_set(v_reuseFailAlloc_1751_, 10, v_platformIndependent_1740_);
lean_ctor_set(v_reuseFailAlloc_1751_, 11, v_dynlibs_1741_);
lean_ctor_set(v_reuseFailAlloc_1751_, 12, v_plugins_1742_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*13, v_buildType_1728_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*13 + 1, v_backend_1739_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1751_, sizeof(void*)*13 + 3, v_allowNonModules_1744_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1763_){
_start:
{
lean_object* v_weakLinkArgs_1764_; 
v_weakLinkArgs_1764_ = lean_ctor_get(v_cfg_1763_, 9);
lean_inc_ref(v_weakLinkArgs_1764_);
return v_weakLinkArgs_1764_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1765_);
lean_dec_ref(v_cfg_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1767_, lean_object* v_cfg_1768_){
_start:
{
uint8_t v_buildType_1769_; lean_object* v_leanOptions_1770_; lean_object* v_moreLeanArgs_1771_; lean_object* v_weakLeanArgs_1772_; lean_object* v_moreLeancArgs_1773_; lean_object* v_moreServerOptions_1774_; lean_object* v_weakLeancArgs_1775_; lean_object* v_moreLinkObjs_1776_; lean_object* v_moreLinkLibs_1777_; lean_object* v_moreLinkArgs_1778_; uint8_t v_backend_1779_; lean_object* v_platformIndependent_1780_; lean_object* v_dynlibs_1781_; lean_object* v_plugins_1782_; uint8_t v_requiresModuleSystem_1783_; uint8_t v_allowNonModules_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_buildType_1769_ = lean_ctor_get_uint8(v_cfg_1768_, sizeof(void*)*13);
v_leanOptions_1770_ = lean_ctor_get(v_cfg_1768_, 0);
v_moreLeanArgs_1771_ = lean_ctor_get(v_cfg_1768_, 1);
v_weakLeanArgs_1772_ = lean_ctor_get(v_cfg_1768_, 2);
v_moreLeancArgs_1773_ = lean_ctor_get(v_cfg_1768_, 3);
v_moreServerOptions_1774_ = lean_ctor_get(v_cfg_1768_, 4);
v_weakLeancArgs_1775_ = lean_ctor_get(v_cfg_1768_, 5);
v_moreLinkObjs_1776_ = lean_ctor_get(v_cfg_1768_, 6);
v_moreLinkLibs_1777_ = lean_ctor_get(v_cfg_1768_, 7);
v_moreLinkArgs_1778_ = lean_ctor_get(v_cfg_1768_, 8);
v_backend_1779_ = lean_ctor_get_uint8(v_cfg_1768_, sizeof(void*)*13 + 1);
v_platformIndependent_1780_ = lean_ctor_get(v_cfg_1768_, 10);
v_dynlibs_1781_ = lean_ctor_get(v_cfg_1768_, 11);
v_plugins_1782_ = lean_ctor_get(v_cfg_1768_, 12);
v_requiresModuleSystem_1783_ = lean_ctor_get_uint8(v_cfg_1768_, sizeof(void*)*13 + 2);
v_allowNonModules_1784_ = lean_ctor_get_uint8(v_cfg_1768_, sizeof(void*)*13 + 3);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_cfg_1768_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_cfg_1768_, 9);
lean_dec(v_unused_1792_);
v___x_1786_ = v_cfg_1768_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_plugins_1782_);
lean_inc(v_dynlibs_1781_);
lean_inc(v_platformIndependent_1780_);
lean_inc(v_moreLinkArgs_1778_);
lean_inc(v_moreLinkLibs_1777_);
lean_inc(v_moreLinkObjs_1776_);
lean_inc(v_weakLeancArgs_1775_);
lean_inc(v_moreServerOptions_1774_);
lean_inc(v_moreLeancArgs_1773_);
lean_inc(v_weakLeanArgs_1772_);
lean_inc(v_moreLeanArgs_1771_);
lean_inc(v_leanOptions_1770_);
lean_dec(v_cfg_1768_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 9, v_val_1767_);
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_leanOptions_1770_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_moreLeanArgs_1771_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_weakLeanArgs_1772_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_moreLeancArgs_1773_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_moreServerOptions_1774_);
lean_ctor_set(v_reuseFailAlloc_1790_, 5, v_weakLeancArgs_1775_);
lean_ctor_set(v_reuseFailAlloc_1790_, 6, v_moreLinkObjs_1776_);
lean_ctor_set(v_reuseFailAlloc_1790_, 7, v_moreLinkLibs_1777_);
lean_ctor_set(v_reuseFailAlloc_1790_, 8, v_moreLinkArgs_1778_);
lean_ctor_set(v_reuseFailAlloc_1790_, 9, v_val_1767_);
lean_ctor_set(v_reuseFailAlloc_1790_, 10, v_platformIndependent_1780_);
lean_ctor_set(v_reuseFailAlloc_1790_, 11, v_dynlibs_1781_);
lean_ctor_set(v_reuseFailAlloc_1790_, 12, v_plugins_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1790_, sizeof(void*)*13, v_buildType_1769_);
lean_ctor_set_uint8(v_reuseFailAlloc_1790_, sizeof(void*)*13 + 1, v_backend_1779_);
lean_ctor_set_uint8(v_reuseFailAlloc_1790_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1783_);
lean_ctor_set_uint8(v_reuseFailAlloc_1790_, sizeof(void*)*13 + 3, v_allowNonModules_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1793_, lean_object* v_cfg_1794_){
_start:
{
uint8_t v_buildType_1795_; lean_object* v_leanOptions_1796_; lean_object* v_moreLeanArgs_1797_; lean_object* v_weakLeanArgs_1798_; lean_object* v_moreLeancArgs_1799_; lean_object* v_moreServerOptions_1800_; lean_object* v_weakLeancArgs_1801_; lean_object* v_moreLinkObjs_1802_; lean_object* v_moreLinkLibs_1803_; lean_object* v_moreLinkArgs_1804_; lean_object* v_weakLinkArgs_1805_; uint8_t v_backend_1806_; lean_object* v_platformIndependent_1807_; lean_object* v_dynlibs_1808_; lean_object* v_plugins_1809_; uint8_t v_requiresModuleSystem_1810_; uint8_t v_allowNonModules_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_buildType_1795_ = lean_ctor_get_uint8(v_cfg_1794_, sizeof(void*)*13);
v_leanOptions_1796_ = lean_ctor_get(v_cfg_1794_, 0);
v_moreLeanArgs_1797_ = lean_ctor_get(v_cfg_1794_, 1);
v_weakLeanArgs_1798_ = lean_ctor_get(v_cfg_1794_, 2);
v_moreLeancArgs_1799_ = lean_ctor_get(v_cfg_1794_, 3);
v_moreServerOptions_1800_ = lean_ctor_get(v_cfg_1794_, 4);
v_weakLeancArgs_1801_ = lean_ctor_get(v_cfg_1794_, 5);
v_moreLinkObjs_1802_ = lean_ctor_get(v_cfg_1794_, 6);
v_moreLinkLibs_1803_ = lean_ctor_get(v_cfg_1794_, 7);
v_moreLinkArgs_1804_ = lean_ctor_get(v_cfg_1794_, 8);
v_weakLinkArgs_1805_ = lean_ctor_get(v_cfg_1794_, 9);
v_backend_1806_ = lean_ctor_get_uint8(v_cfg_1794_, sizeof(void*)*13 + 1);
v_platformIndependent_1807_ = lean_ctor_get(v_cfg_1794_, 10);
v_dynlibs_1808_ = lean_ctor_get(v_cfg_1794_, 11);
v_plugins_1809_ = lean_ctor_get(v_cfg_1794_, 12);
v_requiresModuleSystem_1810_ = lean_ctor_get_uint8(v_cfg_1794_, sizeof(void*)*13 + 2);
v_allowNonModules_1811_ = lean_ctor_get_uint8(v_cfg_1794_, sizeof(void*)*13 + 3);
v_isSharedCheck_1819_ = !lean_is_exclusive(v_cfg_1794_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v_cfg_1794_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_plugins_1809_);
lean_inc(v_dynlibs_1808_);
lean_inc(v_platformIndependent_1807_);
lean_inc(v_weakLinkArgs_1805_);
lean_inc(v_moreLinkArgs_1804_);
lean_inc(v_moreLinkLibs_1803_);
lean_inc(v_moreLinkObjs_1802_);
lean_inc(v_weakLeancArgs_1801_);
lean_inc(v_moreServerOptions_1800_);
lean_inc(v_moreLeancArgs_1799_);
lean_inc(v_weakLeanArgs_1798_);
lean_inc(v_moreLeanArgs_1797_);
lean_inc(v_leanOptions_1796_);
lean_dec(v_cfg_1794_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_apply_1(v_f_1793_, v_weakLinkArgs_1805_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 9, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_leanOptions_1796_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_moreLeanArgs_1797_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_weakLeanArgs_1798_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_moreLeancArgs_1799_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_moreServerOptions_1800_);
lean_ctor_set(v_reuseFailAlloc_1818_, 5, v_weakLeancArgs_1801_);
lean_ctor_set(v_reuseFailAlloc_1818_, 6, v_moreLinkObjs_1802_);
lean_ctor_set(v_reuseFailAlloc_1818_, 7, v_moreLinkLibs_1803_);
lean_ctor_set(v_reuseFailAlloc_1818_, 8, v_moreLinkArgs_1804_);
lean_ctor_set(v_reuseFailAlloc_1818_, 9, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1818_, 10, v_platformIndependent_1807_);
lean_ctor_set(v_reuseFailAlloc_1818_, 11, v_dynlibs_1808_);
lean_ctor_set(v_reuseFailAlloc_1818_, 12, v_plugins_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*13, v_buildType_1795_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*13 + 1, v_backend_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1818_, sizeof(void*)*13 + 3, v_allowNonModules_1811_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1830_){
_start:
{
uint8_t v_backend_1831_; 
v_backend_1831_ = lean_ctor_get_uint8(v_cfg_1830_, sizeof(void*)*13 + 1);
return v_backend_1831_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1832_){
_start:
{
uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_res_1833_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1832_);
lean_dec_ref(v_cfg_1832_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1835_, lean_object* v_cfg_1836_){
_start:
{
uint8_t v_buildType_1837_; lean_object* v_leanOptions_1838_; lean_object* v_moreLeanArgs_1839_; lean_object* v_weakLeanArgs_1840_; lean_object* v_moreLeancArgs_1841_; lean_object* v_moreServerOptions_1842_; lean_object* v_weakLeancArgs_1843_; lean_object* v_moreLinkObjs_1844_; lean_object* v_moreLinkLibs_1845_; lean_object* v_moreLinkArgs_1846_; lean_object* v_weakLinkArgs_1847_; lean_object* v_platformIndependent_1848_; lean_object* v_dynlibs_1849_; lean_object* v_plugins_1850_; uint8_t v_requiresModuleSystem_1851_; uint8_t v_allowNonModules_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_buildType_1837_ = lean_ctor_get_uint8(v_cfg_1836_, sizeof(void*)*13);
v_leanOptions_1838_ = lean_ctor_get(v_cfg_1836_, 0);
v_moreLeanArgs_1839_ = lean_ctor_get(v_cfg_1836_, 1);
v_weakLeanArgs_1840_ = lean_ctor_get(v_cfg_1836_, 2);
v_moreLeancArgs_1841_ = lean_ctor_get(v_cfg_1836_, 3);
v_moreServerOptions_1842_ = lean_ctor_get(v_cfg_1836_, 4);
v_weakLeancArgs_1843_ = lean_ctor_get(v_cfg_1836_, 5);
v_moreLinkObjs_1844_ = lean_ctor_get(v_cfg_1836_, 6);
v_moreLinkLibs_1845_ = lean_ctor_get(v_cfg_1836_, 7);
v_moreLinkArgs_1846_ = lean_ctor_get(v_cfg_1836_, 8);
v_weakLinkArgs_1847_ = lean_ctor_get(v_cfg_1836_, 9);
v_platformIndependent_1848_ = lean_ctor_get(v_cfg_1836_, 10);
v_dynlibs_1849_ = lean_ctor_get(v_cfg_1836_, 11);
v_plugins_1850_ = lean_ctor_get(v_cfg_1836_, 12);
v_requiresModuleSystem_1851_ = lean_ctor_get_uint8(v_cfg_1836_, sizeof(void*)*13 + 2);
v_allowNonModules_1852_ = lean_ctor_get_uint8(v_cfg_1836_, sizeof(void*)*13 + 3);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_cfg_1836_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v_cfg_1836_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_plugins_1850_);
lean_inc(v_dynlibs_1849_);
lean_inc(v_platformIndependent_1848_);
lean_inc(v_weakLinkArgs_1847_);
lean_inc(v_moreLinkArgs_1846_);
lean_inc(v_moreLinkLibs_1845_);
lean_inc(v_moreLinkObjs_1844_);
lean_inc(v_weakLeancArgs_1843_);
lean_inc(v_moreServerOptions_1842_);
lean_inc(v_moreLeancArgs_1841_);
lean_inc(v_weakLeanArgs_1840_);
lean_inc(v_moreLeanArgs_1839_);
lean_inc(v_leanOptions_1838_);
lean_dec(v_cfg_1836_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_leanOptions_1838_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_moreLeanArgs_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_weakLeanArgs_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_moreLeancArgs_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_moreServerOptions_1842_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_weakLeancArgs_1843_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_moreLinkObjs_1844_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_moreLinkLibs_1845_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v_moreLinkArgs_1846_);
lean_ctor_set(v_reuseFailAlloc_1858_, 9, v_weakLinkArgs_1847_);
lean_ctor_set(v_reuseFailAlloc_1858_, 10, v_platformIndependent_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 11, v_dynlibs_1849_);
lean_ctor_set(v_reuseFailAlloc_1858_, 12, v_plugins_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13, v_buildType_1837_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1851_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 3, v_allowNonModules_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*13 + 1, v_val_1835_);
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1860_, lean_object* v_cfg_1861_){
_start:
{
uint8_t v_val_85__boxed_1862_; lean_object* v_res_1863_; 
v_val_85__boxed_1862_ = lean_unbox(v_val_1860_);
v_res_1863_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_85__boxed_1862_, v_cfg_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1864_, lean_object* v_cfg_1865_){
_start:
{
uint8_t v_buildType_1866_; lean_object* v_leanOptions_1867_; lean_object* v_moreLeanArgs_1868_; lean_object* v_weakLeanArgs_1869_; lean_object* v_moreLeancArgs_1870_; lean_object* v_moreServerOptions_1871_; lean_object* v_weakLeancArgs_1872_; lean_object* v_moreLinkObjs_1873_; lean_object* v_moreLinkLibs_1874_; lean_object* v_moreLinkArgs_1875_; lean_object* v_weakLinkArgs_1876_; uint8_t v_backend_1877_; lean_object* v_platformIndependent_1878_; lean_object* v_dynlibs_1879_; lean_object* v_plugins_1880_; uint8_t v_requiresModuleSystem_1881_; uint8_t v_allowNonModules_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1892_; 
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
v_dynlibs_1879_ = lean_ctor_get(v_cfg_1865_, 11);
v_plugins_1880_ = lean_ctor_get(v_cfg_1865_, 12);
v_requiresModuleSystem_1881_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13 + 2);
v_allowNonModules_1882_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13 + 3);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_cfg_1865_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1884_ = v_cfg_1865_;
v_isShared_1885_ = v_isSharedCheck_1892_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_plugins_1880_);
lean_inc(v_dynlibs_1879_);
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
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1892_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1886_ = lean_box(v_backend_1877_);
v___x_1887_ = lean_apply_1(v_f_1864_, v___x_1886_);
if (v_isShared_1885_ == 0)
{
v___x_1889_ = v___x_1884_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_leanOptions_1867_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_moreLeanArgs_1868_);
lean_ctor_set(v_reuseFailAlloc_1891_, 2, v_weakLeanArgs_1869_);
lean_ctor_set(v_reuseFailAlloc_1891_, 3, v_moreLeancArgs_1870_);
lean_ctor_set(v_reuseFailAlloc_1891_, 4, v_moreServerOptions_1871_);
lean_ctor_set(v_reuseFailAlloc_1891_, 5, v_weakLeancArgs_1872_);
lean_ctor_set(v_reuseFailAlloc_1891_, 6, v_moreLinkObjs_1873_);
lean_ctor_set(v_reuseFailAlloc_1891_, 7, v_moreLinkLibs_1874_);
lean_ctor_set(v_reuseFailAlloc_1891_, 8, v_moreLinkArgs_1875_);
lean_ctor_set(v_reuseFailAlloc_1891_, 9, v_weakLinkArgs_1876_);
lean_ctor_set(v_reuseFailAlloc_1891_, 10, v_platformIndependent_1878_);
lean_ctor_set(v_reuseFailAlloc_1891_, 11, v_dynlibs_1879_);
lean_ctor_set(v_reuseFailAlloc_1891_, 12, v_plugins_1880_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*13, v_buildType_1866_);
v___x_1889_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_unbox(v___x_1887_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*13 + 1, v___x_1890_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1881_);
lean_ctor_set_uint8(v___x_1889_, sizeof(void*)*13 + 3, v_allowNonModules_1882_);
return v___x_1889_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = 2;
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1895_){
_start:
{
uint8_t v_res_1896_; lean_object* v_r_1897_; 
v_res_1896_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1895_);
lean_dec_ref(v_x_1895_);
v_r_1897_ = lean_box(v_res_1896_);
return v_r_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1909_){
_start:
{
lean_object* v_platformIndependent_1910_; 
v_platformIndependent_1910_ = lean_ctor_get(v_cfg_1909_, 10);
lean_inc(v_platformIndependent_1910_);
return v_platformIndependent_1910_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1911_);
lean_dec_ref(v_cfg_1911_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1913_, lean_object* v_cfg_1914_){
_start:
{
uint8_t v_buildType_1915_; lean_object* v_leanOptions_1916_; lean_object* v_moreLeanArgs_1917_; lean_object* v_weakLeanArgs_1918_; lean_object* v_moreLeancArgs_1919_; lean_object* v_moreServerOptions_1920_; lean_object* v_weakLeancArgs_1921_; lean_object* v_moreLinkObjs_1922_; lean_object* v_moreLinkLibs_1923_; lean_object* v_moreLinkArgs_1924_; lean_object* v_weakLinkArgs_1925_; uint8_t v_backend_1926_; lean_object* v_dynlibs_1927_; lean_object* v_plugins_1928_; uint8_t v_requiresModuleSystem_1929_; uint8_t v_allowNonModules_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_buildType_1915_ = lean_ctor_get_uint8(v_cfg_1914_, sizeof(void*)*13);
v_leanOptions_1916_ = lean_ctor_get(v_cfg_1914_, 0);
v_moreLeanArgs_1917_ = lean_ctor_get(v_cfg_1914_, 1);
v_weakLeanArgs_1918_ = lean_ctor_get(v_cfg_1914_, 2);
v_moreLeancArgs_1919_ = lean_ctor_get(v_cfg_1914_, 3);
v_moreServerOptions_1920_ = lean_ctor_get(v_cfg_1914_, 4);
v_weakLeancArgs_1921_ = lean_ctor_get(v_cfg_1914_, 5);
v_moreLinkObjs_1922_ = lean_ctor_get(v_cfg_1914_, 6);
v_moreLinkLibs_1923_ = lean_ctor_get(v_cfg_1914_, 7);
v_moreLinkArgs_1924_ = lean_ctor_get(v_cfg_1914_, 8);
v_weakLinkArgs_1925_ = lean_ctor_get(v_cfg_1914_, 9);
v_backend_1926_ = lean_ctor_get_uint8(v_cfg_1914_, sizeof(void*)*13 + 1);
v_dynlibs_1927_ = lean_ctor_get(v_cfg_1914_, 11);
v_plugins_1928_ = lean_ctor_get(v_cfg_1914_, 12);
v_requiresModuleSystem_1929_ = lean_ctor_get_uint8(v_cfg_1914_, sizeof(void*)*13 + 2);
v_allowNonModules_1930_ = lean_ctor_get_uint8(v_cfg_1914_, sizeof(void*)*13 + 3);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_cfg_1914_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_cfg_1914_, 10);
lean_dec(v_unused_1938_);
v___x_1932_ = v_cfg_1914_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_plugins_1928_);
lean_inc(v_dynlibs_1927_);
lean_inc(v_weakLinkArgs_1925_);
lean_inc(v_moreLinkArgs_1924_);
lean_inc(v_moreLinkLibs_1923_);
lean_inc(v_moreLinkObjs_1922_);
lean_inc(v_weakLeancArgs_1921_);
lean_inc(v_moreServerOptions_1920_);
lean_inc(v_moreLeancArgs_1919_);
lean_inc(v_weakLeanArgs_1918_);
lean_inc(v_moreLeanArgs_1917_);
lean_inc(v_leanOptions_1916_);
lean_dec(v_cfg_1914_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 10, v_val_1913_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_leanOptions_1916_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_moreLeanArgs_1917_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_weakLeanArgs_1918_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_moreLeancArgs_1919_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v_moreServerOptions_1920_);
lean_ctor_set(v_reuseFailAlloc_1936_, 5, v_weakLeancArgs_1921_);
lean_ctor_set(v_reuseFailAlloc_1936_, 6, v_moreLinkObjs_1922_);
lean_ctor_set(v_reuseFailAlloc_1936_, 7, v_moreLinkLibs_1923_);
lean_ctor_set(v_reuseFailAlloc_1936_, 8, v_moreLinkArgs_1924_);
lean_ctor_set(v_reuseFailAlloc_1936_, 9, v_weakLinkArgs_1925_);
lean_ctor_set(v_reuseFailAlloc_1936_, 10, v_val_1913_);
lean_ctor_set(v_reuseFailAlloc_1936_, 11, v_dynlibs_1927_);
lean_ctor_set(v_reuseFailAlloc_1936_, 12, v_plugins_1928_);
lean_ctor_set_uint8(v_reuseFailAlloc_1936_, sizeof(void*)*13, v_buildType_1915_);
lean_ctor_set_uint8(v_reuseFailAlloc_1936_, sizeof(void*)*13 + 1, v_backend_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1936_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1929_);
lean_ctor_set_uint8(v_reuseFailAlloc_1936_, sizeof(void*)*13 + 3, v_allowNonModules_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_1939_, lean_object* v_cfg_1940_){
_start:
{
uint8_t v_buildType_1941_; lean_object* v_leanOptions_1942_; lean_object* v_moreLeanArgs_1943_; lean_object* v_weakLeanArgs_1944_; lean_object* v_moreLeancArgs_1945_; lean_object* v_moreServerOptions_1946_; lean_object* v_weakLeancArgs_1947_; lean_object* v_moreLinkObjs_1948_; lean_object* v_moreLinkLibs_1949_; lean_object* v_moreLinkArgs_1950_; lean_object* v_weakLinkArgs_1951_; uint8_t v_backend_1952_; lean_object* v_platformIndependent_1953_; lean_object* v_dynlibs_1954_; lean_object* v_plugins_1955_; uint8_t v_requiresModuleSystem_1956_; uint8_t v_allowNonModules_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1965_; 
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
v_dynlibs_1954_ = lean_ctor_get(v_cfg_1940_, 11);
v_plugins_1955_ = lean_ctor_get(v_cfg_1940_, 12);
v_requiresModuleSystem_1956_ = lean_ctor_get_uint8(v_cfg_1940_, sizeof(void*)*13 + 2);
v_allowNonModules_1957_ = lean_ctor_get_uint8(v_cfg_1940_, sizeof(void*)*13 + 3);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_cfg_1940_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1959_ = v_cfg_1940_;
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_plugins_1955_);
lean_inc(v_dynlibs_1954_);
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
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1965_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v___x_1963_; 
v___x_1961_ = lean_apply_1(v_f_1939_, v_platformIndependent_1953_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 10, v___x_1961_);
v___x_1963_ = v___x_1959_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_leanOptions_1942_);
lean_ctor_set(v_reuseFailAlloc_1964_, 1, v_moreLeanArgs_1943_);
lean_ctor_set(v_reuseFailAlloc_1964_, 2, v_weakLeanArgs_1944_);
lean_ctor_set(v_reuseFailAlloc_1964_, 3, v_moreLeancArgs_1945_);
lean_ctor_set(v_reuseFailAlloc_1964_, 4, v_moreServerOptions_1946_);
lean_ctor_set(v_reuseFailAlloc_1964_, 5, v_weakLeancArgs_1947_);
lean_ctor_set(v_reuseFailAlloc_1964_, 6, v_moreLinkObjs_1948_);
lean_ctor_set(v_reuseFailAlloc_1964_, 7, v_moreLinkLibs_1949_);
lean_ctor_set(v_reuseFailAlloc_1964_, 8, v_moreLinkArgs_1950_);
lean_ctor_set(v_reuseFailAlloc_1964_, 9, v_weakLinkArgs_1951_);
lean_ctor_set(v_reuseFailAlloc_1964_, 10, v___x_1961_);
lean_ctor_set(v_reuseFailAlloc_1964_, 11, v_dynlibs_1954_);
lean_ctor_set(v_reuseFailAlloc_1964_, 12, v_plugins_1955_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*13, v_buildType_1941_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*13 + 1, v_backend_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1956_);
lean_ctor_set_uint8(v_reuseFailAlloc_1964_, sizeof(void*)*13 + 3, v_allowNonModules_1957_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_box(0);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_1968_);
lean_dec_ref(v_x_1968_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_1981_){
_start:
{
lean_object* v_dynlibs_1982_; 
v_dynlibs_1982_ = lean_ctor_get(v_cfg_1981_, 11);
lean_inc_ref(v_dynlibs_1982_);
return v_dynlibs_1982_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_1983_);
lean_dec_ref(v_cfg_1983_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_1985_, lean_object* v_cfg_1986_){
_start:
{
uint8_t v_buildType_1987_; lean_object* v_leanOptions_1988_; lean_object* v_moreLeanArgs_1989_; lean_object* v_weakLeanArgs_1990_; lean_object* v_moreLeancArgs_1991_; lean_object* v_moreServerOptions_1992_; lean_object* v_weakLeancArgs_1993_; lean_object* v_moreLinkObjs_1994_; lean_object* v_moreLinkLibs_1995_; lean_object* v_moreLinkArgs_1996_; lean_object* v_weakLinkArgs_1997_; uint8_t v_backend_1998_; lean_object* v_platformIndependent_1999_; lean_object* v_plugins_2000_; uint8_t v_requiresModuleSystem_2001_; uint8_t v_allowNonModules_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_buildType_1987_ = lean_ctor_get_uint8(v_cfg_1986_, sizeof(void*)*13);
v_leanOptions_1988_ = lean_ctor_get(v_cfg_1986_, 0);
v_moreLeanArgs_1989_ = lean_ctor_get(v_cfg_1986_, 1);
v_weakLeanArgs_1990_ = lean_ctor_get(v_cfg_1986_, 2);
v_moreLeancArgs_1991_ = lean_ctor_get(v_cfg_1986_, 3);
v_moreServerOptions_1992_ = lean_ctor_get(v_cfg_1986_, 4);
v_weakLeancArgs_1993_ = lean_ctor_get(v_cfg_1986_, 5);
v_moreLinkObjs_1994_ = lean_ctor_get(v_cfg_1986_, 6);
v_moreLinkLibs_1995_ = lean_ctor_get(v_cfg_1986_, 7);
v_moreLinkArgs_1996_ = lean_ctor_get(v_cfg_1986_, 8);
v_weakLinkArgs_1997_ = lean_ctor_get(v_cfg_1986_, 9);
v_backend_1998_ = lean_ctor_get_uint8(v_cfg_1986_, sizeof(void*)*13 + 1);
v_platformIndependent_1999_ = lean_ctor_get(v_cfg_1986_, 10);
v_plugins_2000_ = lean_ctor_get(v_cfg_1986_, 12);
v_requiresModuleSystem_2001_ = lean_ctor_get_uint8(v_cfg_1986_, sizeof(void*)*13 + 2);
v_allowNonModules_2002_ = lean_ctor_get_uint8(v_cfg_1986_, sizeof(void*)*13 + 3);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_cfg_1986_);
if (v_isSharedCheck_2009_ == 0)
{
lean_object* v_unused_2010_; 
v_unused_2010_ = lean_ctor_get(v_cfg_1986_, 11);
lean_dec(v_unused_2010_);
v___x_2004_ = v_cfg_1986_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_plugins_2000_);
lean_inc(v_platformIndependent_1999_);
lean_inc(v_weakLinkArgs_1997_);
lean_inc(v_moreLinkArgs_1996_);
lean_inc(v_moreLinkLibs_1995_);
lean_inc(v_moreLinkObjs_1994_);
lean_inc(v_weakLeancArgs_1993_);
lean_inc(v_moreServerOptions_1992_);
lean_inc(v_moreLeancArgs_1991_);
lean_inc(v_weakLeanArgs_1990_);
lean_inc(v_moreLeanArgs_1989_);
lean_inc(v_leanOptions_1988_);
lean_dec(v_cfg_1986_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 11, v_val_1985_);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_leanOptions_1988_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_moreLeanArgs_1989_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_weakLeanArgs_1990_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_moreLeancArgs_1991_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_moreServerOptions_1992_);
lean_ctor_set(v_reuseFailAlloc_2008_, 5, v_weakLeancArgs_1993_);
lean_ctor_set(v_reuseFailAlloc_2008_, 6, v_moreLinkObjs_1994_);
lean_ctor_set(v_reuseFailAlloc_2008_, 7, v_moreLinkLibs_1995_);
lean_ctor_set(v_reuseFailAlloc_2008_, 8, v_moreLinkArgs_1996_);
lean_ctor_set(v_reuseFailAlloc_2008_, 9, v_weakLinkArgs_1997_);
lean_ctor_set(v_reuseFailAlloc_2008_, 10, v_platformIndependent_1999_);
lean_ctor_set(v_reuseFailAlloc_2008_, 11, v_val_1985_);
lean_ctor_set(v_reuseFailAlloc_2008_, 12, v_plugins_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13, v_buildType_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13 + 1, v_backend_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2001_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13 + 3, v_allowNonModules_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_2011_, lean_object* v_cfg_2012_){
_start:
{
uint8_t v_buildType_2013_; lean_object* v_leanOptions_2014_; lean_object* v_moreLeanArgs_2015_; lean_object* v_weakLeanArgs_2016_; lean_object* v_moreLeancArgs_2017_; lean_object* v_moreServerOptions_2018_; lean_object* v_weakLeancArgs_2019_; lean_object* v_moreLinkObjs_2020_; lean_object* v_moreLinkLibs_2021_; lean_object* v_moreLinkArgs_2022_; lean_object* v_weakLinkArgs_2023_; uint8_t v_backend_2024_; lean_object* v_platformIndependent_2025_; lean_object* v_dynlibs_2026_; lean_object* v_plugins_2027_; uint8_t v_requiresModuleSystem_2028_; uint8_t v_allowNonModules_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2037_; 
v_buildType_2013_ = lean_ctor_get_uint8(v_cfg_2012_, sizeof(void*)*13);
v_leanOptions_2014_ = lean_ctor_get(v_cfg_2012_, 0);
v_moreLeanArgs_2015_ = lean_ctor_get(v_cfg_2012_, 1);
v_weakLeanArgs_2016_ = lean_ctor_get(v_cfg_2012_, 2);
v_moreLeancArgs_2017_ = lean_ctor_get(v_cfg_2012_, 3);
v_moreServerOptions_2018_ = lean_ctor_get(v_cfg_2012_, 4);
v_weakLeancArgs_2019_ = lean_ctor_get(v_cfg_2012_, 5);
v_moreLinkObjs_2020_ = lean_ctor_get(v_cfg_2012_, 6);
v_moreLinkLibs_2021_ = lean_ctor_get(v_cfg_2012_, 7);
v_moreLinkArgs_2022_ = lean_ctor_get(v_cfg_2012_, 8);
v_weakLinkArgs_2023_ = lean_ctor_get(v_cfg_2012_, 9);
v_backend_2024_ = lean_ctor_get_uint8(v_cfg_2012_, sizeof(void*)*13 + 1);
v_platformIndependent_2025_ = lean_ctor_get(v_cfg_2012_, 10);
v_dynlibs_2026_ = lean_ctor_get(v_cfg_2012_, 11);
v_plugins_2027_ = lean_ctor_get(v_cfg_2012_, 12);
v_requiresModuleSystem_2028_ = lean_ctor_get_uint8(v_cfg_2012_, sizeof(void*)*13 + 2);
v_allowNonModules_2029_ = lean_ctor_get_uint8(v_cfg_2012_, sizeof(void*)*13 + 3);
v_isSharedCheck_2037_ = !lean_is_exclusive(v_cfg_2012_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2031_ = v_cfg_2012_;
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_plugins_2027_);
lean_inc(v_dynlibs_2026_);
lean_inc(v_platformIndependent_2025_);
lean_inc(v_weakLinkArgs_2023_);
lean_inc(v_moreLinkArgs_2022_);
lean_inc(v_moreLinkLibs_2021_);
lean_inc(v_moreLinkObjs_2020_);
lean_inc(v_weakLeancArgs_2019_);
lean_inc(v_moreServerOptions_2018_);
lean_inc(v_moreLeancArgs_2017_);
lean_inc(v_weakLeanArgs_2016_);
lean_inc(v_moreLeanArgs_2015_);
lean_inc(v_leanOptions_2014_);
lean_dec(v_cfg_2012_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2037_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = lean_apply_1(v_f_2011_, v_dynlibs_2026_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 11, v___x_2033_);
v___x_2035_ = v___x_2031_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_leanOptions_2014_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_moreLeanArgs_2015_);
lean_ctor_set(v_reuseFailAlloc_2036_, 2, v_weakLeanArgs_2016_);
lean_ctor_set(v_reuseFailAlloc_2036_, 3, v_moreLeancArgs_2017_);
lean_ctor_set(v_reuseFailAlloc_2036_, 4, v_moreServerOptions_2018_);
lean_ctor_set(v_reuseFailAlloc_2036_, 5, v_weakLeancArgs_2019_);
lean_ctor_set(v_reuseFailAlloc_2036_, 6, v_moreLinkObjs_2020_);
lean_ctor_set(v_reuseFailAlloc_2036_, 7, v_moreLinkLibs_2021_);
lean_ctor_set(v_reuseFailAlloc_2036_, 8, v_moreLinkArgs_2022_);
lean_ctor_set(v_reuseFailAlloc_2036_, 9, v_weakLinkArgs_2023_);
lean_ctor_set(v_reuseFailAlloc_2036_, 10, v_platformIndependent_2025_);
lean_ctor_set(v_reuseFailAlloc_2036_, 11, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2036_, 12, v_plugins_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*13, v_buildType_2013_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*13 + 1, v_backend_2024_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2028_);
lean_ctor_set_uint8(v_reuseFailAlloc_2036_, sizeof(void*)*13 + 3, v_allowNonModules_2029_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_2048_){
_start:
{
lean_object* v_plugins_2049_; 
v_plugins_2049_ = lean_ctor_get(v_cfg_2048_, 12);
lean_inc_ref(v_plugins_2049_);
return v_plugins_2049_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_2050_);
lean_dec_ref(v_cfg_2050_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_2052_, lean_object* v_cfg_2053_){
_start:
{
uint8_t v_buildType_2054_; lean_object* v_leanOptions_2055_; lean_object* v_moreLeanArgs_2056_; lean_object* v_weakLeanArgs_2057_; lean_object* v_moreLeancArgs_2058_; lean_object* v_moreServerOptions_2059_; lean_object* v_weakLeancArgs_2060_; lean_object* v_moreLinkObjs_2061_; lean_object* v_moreLinkLibs_2062_; lean_object* v_moreLinkArgs_2063_; lean_object* v_weakLinkArgs_2064_; uint8_t v_backend_2065_; lean_object* v_platformIndependent_2066_; lean_object* v_dynlibs_2067_; uint8_t v_requiresModuleSystem_2068_; uint8_t v_allowNonModules_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
v_buildType_2054_ = lean_ctor_get_uint8(v_cfg_2053_, sizeof(void*)*13);
v_leanOptions_2055_ = lean_ctor_get(v_cfg_2053_, 0);
v_moreLeanArgs_2056_ = lean_ctor_get(v_cfg_2053_, 1);
v_weakLeanArgs_2057_ = lean_ctor_get(v_cfg_2053_, 2);
v_moreLeancArgs_2058_ = lean_ctor_get(v_cfg_2053_, 3);
v_moreServerOptions_2059_ = lean_ctor_get(v_cfg_2053_, 4);
v_weakLeancArgs_2060_ = lean_ctor_get(v_cfg_2053_, 5);
v_moreLinkObjs_2061_ = lean_ctor_get(v_cfg_2053_, 6);
v_moreLinkLibs_2062_ = lean_ctor_get(v_cfg_2053_, 7);
v_moreLinkArgs_2063_ = lean_ctor_get(v_cfg_2053_, 8);
v_weakLinkArgs_2064_ = lean_ctor_get(v_cfg_2053_, 9);
v_backend_2065_ = lean_ctor_get_uint8(v_cfg_2053_, sizeof(void*)*13 + 1);
v_platformIndependent_2066_ = lean_ctor_get(v_cfg_2053_, 10);
v_dynlibs_2067_ = lean_ctor_get(v_cfg_2053_, 11);
v_requiresModuleSystem_2068_ = lean_ctor_get_uint8(v_cfg_2053_, sizeof(void*)*13 + 2);
v_allowNonModules_2069_ = lean_ctor_get_uint8(v_cfg_2053_, sizeof(void*)*13 + 3);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_cfg_2053_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_cfg_2053_, 12);
lean_dec(v_unused_2077_);
v___x_2071_ = v_cfg_2053_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_dynlibs_2067_);
lean_inc(v_platformIndependent_2066_);
lean_inc(v_weakLinkArgs_2064_);
lean_inc(v_moreLinkArgs_2063_);
lean_inc(v_moreLinkLibs_2062_);
lean_inc(v_moreLinkObjs_2061_);
lean_inc(v_weakLeancArgs_2060_);
lean_inc(v_moreServerOptions_2059_);
lean_inc(v_moreLeancArgs_2058_);
lean_inc(v_weakLeanArgs_2057_);
lean_inc(v_moreLeanArgs_2056_);
lean_inc(v_leanOptions_2055_);
lean_dec(v_cfg_2053_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 12, v_val_2052_);
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_leanOptions_2055_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_moreLeanArgs_2056_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_weakLeanArgs_2057_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_moreLeancArgs_2058_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v_moreServerOptions_2059_);
lean_ctor_set(v_reuseFailAlloc_2075_, 5, v_weakLeancArgs_2060_);
lean_ctor_set(v_reuseFailAlloc_2075_, 6, v_moreLinkObjs_2061_);
lean_ctor_set(v_reuseFailAlloc_2075_, 7, v_moreLinkLibs_2062_);
lean_ctor_set(v_reuseFailAlloc_2075_, 8, v_moreLinkArgs_2063_);
lean_ctor_set(v_reuseFailAlloc_2075_, 9, v_weakLinkArgs_2064_);
lean_ctor_set(v_reuseFailAlloc_2075_, 10, v_platformIndependent_2066_);
lean_ctor_set(v_reuseFailAlloc_2075_, 11, v_dynlibs_2067_);
lean_ctor_set(v_reuseFailAlloc_2075_, 12, v_val_2052_);
lean_ctor_set_uint8(v_reuseFailAlloc_2075_, sizeof(void*)*13, v_buildType_2054_);
lean_ctor_set_uint8(v_reuseFailAlloc_2075_, sizeof(void*)*13 + 1, v_backend_2065_);
lean_ctor_set_uint8(v_reuseFailAlloc_2075_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2068_);
lean_ctor_set_uint8(v_reuseFailAlloc_2075_, sizeof(void*)*13 + 3, v_allowNonModules_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_2078_, lean_object* v_cfg_2079_){
_start:
{
uint8_t v_buildType_2080_; lean_object* v_leanOptions_2081_; lean_object* v_moreLeanArgs_2082_; lean_object* v_weakLeanArgs_2083_; lean_object* v_moreLeancArgs_2084_; lean_object* v_moreServerOptions_2085_; lean_object* v_weakLeancArgs_2086_; lean_object* v_moreLinkObjs_2087_; lean_object* v_moreLinkLibs_2088_; lean_object* v_moreLinkArgs_2089_; lean_object* v_weakLinkArgs_2090_; uint8_t v_backend_2091_; lean_object* v_platformIndependent_2092_; lean_object* v_dynlibs_2093_; lean_object* v_plugins_2094_; uint8_t v_requiresModuleSystem_2095_; uint8_t v_allowNonModules_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2104_; 
v_buildType_2080_ = lean_ctor_get_uint8(v_cfg_2079_, sizeof(void*)*13);
v_leanOptions_2081_ = lean_ctor_get(v_cfg_2079_, 0);
v_moreLeanArgs_2082_ = lean_ctor_get(v_cfg_2079_, 1);
v_weakLeanArgs_2083_ = lean_ctor_get(v_cfg_2079_, 2);
v_moreLeancArgs_2084_ = lean_ctor_get(v_cfg_2079_, 3);
v_moreServerOptions_2085_ = lean_ctor_get(v_cfg_2079_, 4);
v_weakLeancArgs_2086_ = lean_ctor_get(v_cfg_2079_, 5);
v_moreLinkObjs_2087_ = lean_ctor_get(v_cfg_2079_, 6);
v_moreLinkLibs_2088_ = lean_ctor_get(v_cfg_2079_, 7);
v_moreLinkArgs_2089_ = lean_ctor_get(v_cfg_2079_, 8);
v_weakLinkArgs_2090_ = lean_ctor_get(v_cfg_2079_, 9);
v_backend_2091_ = lean_ctor_get_uint8(v_cfg_2079_, sizeof(void*)*13 + 1);
v_platformIndependent_2092_ = lean_ctor_get(v_cfg_2079_, 10);
v_dynlibs_2093_ = lean_ctor_get(v_cfg_2079_, 11);
v_plugins_2094_ = lean_ctor_get(v_cfg_2079_, 12);
v_requiresModuleSystem_2095_ = lean_ctor_get_uint8(v_cfg_2079_, sizeof(void*)*13 + 2);
v_allowNonModules_2096_ = lean_ctor_get_uint8(v_cfg_2079_, sizeof(void*)*13 + 3);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_cfg_2079_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2098_ = v_cfg_2079_;
v_isShared_2099_ = v_isSharedCheck_2104_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_plugins_2094_);
lean_inc(v_dynlibs_2093_);
lean_inc(v_platformIndependent_2092_);
lean_inc(v_weakLinkArgs_2090_);
lean_inc(v_moreLinkArgs_2089_);
lean_inc(v_moreLinkLibs_2088_);
lean_inc(v_moreLinkObjs_2087_);
lean_inc(v_weakLeancArgs_2086_);
lean_inc(v_moreServerOptions_2085_);
lean_inc(v_moreLeancArgs_2084_);
lean_inc(v_weakLeanArgs_2083_);
lean_inc(v_moreLeanArgs_2082_);
lean_inc(v_leanOptions_2081_);
lean_dec(v_cfg_2079_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2104_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2100_ = lean_apply_1(v_f_2078_, v_plugins_2094_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 12, v___x_2100_);
v___x_2102_ = v___x_2098_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_leanOptions_2081_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_moreLeanArgs_2082_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_weakLeanArgs_2083_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_moreLeancArgs_2084_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_moreServerOptions_2085_);
lean_ctor_set(v_reuseFailAlloc_2103_, 5, v_weakLeancArgs_2086_);
lean_ctor_set(v_reuseFailAlloc_2103_, 6, v_moreLinkObjs_2087_);
lean_ctor_set(v_reuseFailAlloc_2103_, 7, v_moreLinkLibs_2088_);
lean_ctor_set(v_reuseFailAlloc_2103_, 8, v_moreLinkArgs_2089_);
lean_ctor_set(v_reuseFailAlloc_2103_, 9, v_weakLinkArgs_2090_);
lean_ctor_set(v_reuseFailAlloc_2103_, 10, v_platformIndependent_2092_);
lean_ctor_set(v_reuseFailAlloc_2103_, 11, v_dynlibs_2093_);
lean_ctor_set(v_reuseFailAlloc_2103_, 12, v___x_2100_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13, v_buildType_2080_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 1, v_backend_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2095_);
lean_ctor_set_uint8(v_reuseFailAlloc_2103_, sizeof(void*)*13 + 3, v_allowNonModules_2096_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object* v_cfg_2115_){
_start:
{
uint8_t v_requiresModuleSystem_2116_; 
v_requiresModuleSystem_2116_ = lean_ctor_get_uint8(v_cfg_2115_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_2116_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object* v_cfg_2117_){
_start:
{
uint8_t v_res_2118_; lean_object* v_r_2119_; 
v_res_2118_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2117_);
lean_dec_ref(v_cfg_2117_);
v_r_2119_ = lean_box(v_res_2118_);
return v_r_2119_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t v_val_2120_, lean_object* v_cfg_2121_){
_start:
{
uint8_t v_buildType_2122_; lean_object* v_leanOptions_2123_; lean_object* v_moreLeanArgs_2124_; lean_object* v_weakLeanArgs_2125_; lean_object* v_moreLeancArgs_2126_; lean_object* v_moreServerOptions_2127_; lean_object* v_weakLeancArgs_2128_; lean_object* v_moreLinkObjs_2129_; lean_object* v_moreLinkLibs_2130_; lean_object* v_moreLinkArgs_2131_; lean_object* v_weakLinkArgs_2132_; uint8_t v_backend_2133_; lean_object* v_platformIndependent_2134_; lean_object* v_dynlibs_2135_; lean_object* v_plugins_2136_; uint8_t v_allowNonModules_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
v_buildType_2122_ = lean_ctor_get_uint8(v_cfg_2121_, sizeof(void*)*13);
v_leanOptions_2123_ = lean_ctor_get(v_cfg_2121_, 0);
v_moreLeanArgs_2124_ = lean_ctor_get(v_cfg_2121_, 1);
v_weakLeanArgs_2125_ = lean_ctor_get(v_cfg_2121_, 2);
v_moreLeancArgs_2126_ = lean_ctor_get(v_cfg_2121_, 3);
v_moreServerOptions_2127_ = lean_ctor_get(v_cfg_2121_, 4);
v_weakLeancArgs_2128_ = lean_ctor_get(v_cfg_2121_, 5);
v_moreLinkObjs_2129_ = lean_ctor_get(v_cfg_2121_, 6);
v_moreLinkLibs_2130_ = lean_ctor_get(v_cfg_2121_, 7);
v_moreLinkArgs_2131_ = lean_ctor_get(v_cfg_2121_, 8);
v_weakLinkArgs_2132_ = lean_ctor_get(v_cfg_2121_, 9);
v_backend_2133_ = lean_ctor_get_uint8(v_cfg_2121_, sizeof(void*)*13 + 1);
v_platformIndependent_2134_ = lean_ctor_get(v_cfg_2121_, 10);
v_dynlibs_2135_ = lean_ctor_get(v_cfg_2121_, 11);
v_plugins_2136_ = lean_ctor_get(v_cfg_2121_, 12);
v_allowNonModules_2137_ = lean_ctor_get_uint8(v_cfg_2121_, sizeof(void*)*13 + 3);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_cfg_2121_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v_cfg_2121_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_plugins_2136_);
lean_inc(v_dynlibs_2135_);
lean_inc(v_platformIndependent_2134_);
lean_inc(v_weakLinkArgs_2132_);
lean_inc(v_moreLinkArgs_2131_);
lean_inc(v_moreLinkLibs_2130_);
lean_inc(v_moreLinkObjs_2129_);
lean_inc(v_weakLeancArgs_2128_);
lean_inc(v_moreServerOptions_2127_);
lean_inc(v_moreLeancArgs_2126_);
lean_inc(v_weakLeanArgs_2125_);
lean_inc(v_moreLeanArgs_2124_);
lean_inc(v_leanOptions_2123_);
lean_dec(v_cfg_2121_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_leanOptions_2123_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_moreLeanArgs_2124_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_weakLeanArgs_2125_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_moreLeancArgs_2126_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_moreServerOptions_2127_);
lean_ctor_set(v_reuseFailAlloc_2143_, 5, v_weakLeancArgs_2128_);
lean_ctor_set(v_reuseFailAlloc_2143_, 6, v_moreLinkObjs_2129_);
lean_ctor_set(v_reuseFailAlloc_2143_, 7, v_moreLinkLibs_2130_);
lean_ctor_set(v_reuseFailAlloc_2143_, 8, v_moreLinkArgs_2131_);
lean_ctor_set(v_reuseFailAlloc_2143_, 9, v_weakLinkArgs_2132_);
lean_ctor_set(v_reuseFailAlloc_2143_, 10, v_platformIndependent_2134_);
lean_ctor_set(v_reuseFailAlloc_2143_, 11, v_dynlibs_2135_);
lean_ctor_set(v_reuseFailAlloc_2143_, 12, v_plugins_2136_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*13, v_buildType_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*13 + 1, v_backend_2133_);
lean_ctor_set_uint8(v_reuseFailAlloc_2143_, sizeof(void*)*13 + 3, v_allowNonModules_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
lean_ctor_set_uint8(v___x_2142_, sizeof(void*)*13 + 2, v_val_2120_);
return v___x_2142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object* v_val_2145_, lean_object* v_cfg_2146_){
_start:
{
uint8_t v_val_85__boxed_2147_; lean_object* v_res_2148_; 
v_val_85__boxed_2147_ = lean_unbox(v_val_2145_);
v_res_2148_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_85__boxed_2147_, v_cfg_2146_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object* v_f_2149_, lean_object* v_cfg_2150_){
_start:
{
uint8_t v_buildType_2151_; lean_object* v_leanOptions_2152_; lean_object* v_moreLeanArgs_2153_; lean_object* v_weakLeanArgs_2154_; lean_object* v_moreLeancArgs_2155_; lean_object* v_moreServerOptions_2156_; lean_object* v_weakLeancArgs_2157_; lean_object* v_moreLinkObjs_2158_; lean_object* v_moreLinkLibs_2159_; lean_object* v_moreLinkArgs_2160_; lean_object* v_weakLinkArgs_2161_; uint8_t v_backend_2162_; lean_object* v_platformIndependent_2163_; lean_object* v_dynlibs_2164_; lean_object* v_plugins_2165_; uint8_t v_requiresModuleSystem_2166_; uint8_t v_allowNonModules_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2177_; 
v_buildType_2151_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*13);
v_leanOptions_2152_ = lean_ctor_get(v_cfg_2150_, 0);
v_moreLeanArgs_2153_ = lean_ctor_get(v_cfg_2150_, 1);
v_weakLeanArgs_2154_ = lean_ctor_get(v_cfg_2150_, 2);
v_moreLeancArgs_2155_ = lean_ctor_get(v_cfg_2150_, 3);
v_moreServerOptions_2156_ = lean_ctor_get(v_cfg_2150_, 4);
v_weakLeancArgs_2157_ = lean_ctor_get(v_cfg_2150_, 5);
v_moreLinkObjs_2158_ = lean_ctor_get(v_cfg_2150_, 6);
v_moreLinkLibs_2159_ = lean_ctor_get(v_cfg_2150_, 7);
v_moreLinkArgs_2160_ = lean_ctor_get(v_cfg_2150_, 8);
v_weakLinkArgs_2161_ = lean_ctor_get(v_cfg_2150_, 9);
v_backend_2162_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*13 + 1);
v_platformIndependent_2163_ = lean_ctor_get(v_cfg_2150_, 10);
v_dynlibs_2164_ = lean_ctor_get(v_cfg_2150_, 11);
v_plugins_2165_ = lean_ctor_get(v_cfg_2150_, 12);
v_requiresModuleSystem_2166_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*13 + 2);
v_allowNonModules_2167_ = lean_ctor_get_uint8(v_cfg_2150_, sizeof(void*)*13 + 3);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_cfg_2150_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2169_ = v_cfg_2150_;
v_isShared_2170_ = v_isSharedCheck_2177_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_plugins_2165_);
lean_inc(v_dynlibs_2164_);
lean_inc(v_platformIndependent_2163_);
lean_inc(v_weakLinkArgs_2161_);
lean_inc(v_moreLinkArgs_2160_);
lean_inc(v_moreLinkLibs_2159_);
lean_inc(v_moreLinkObjs_2158_);
lean_inc(v_weakLeancArgs_2157_);
lean_inc(v_moreServerOptions_2156_);
lean_inc(v_moreLeancArgs_2155_);
lean_inc(v_weakLeanArgs_2154_);
lean_inc(v_moreLeanArgs_2153_);
lean_inc(v_leanOptions_2152_);
lean_dec(v_cfg_2150_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2177_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2171_ = lean_box(v_requiresModuleSystem_2166_);
v___x_2172_ = lean_apply_1(v_f_2149_, v___x_2171_);
if (v_isShared_2170_ == 0)
{
v___x_2174_ = v___x_2169_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_leanOptions_2152_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_moreLeanArgs_2153_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_weakLeanArgs_2154_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v_moreLeancArgs_2155_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v_moreServerOptions_2156_);
lean_ctor_set(v_reuseFailAlloc_2176_, 5, v_weakLeancArgs_2157_);
lean_ctor_set(v_reuseFailAlloc_2176_, 6, v_moreLinkObjs_2158_);
lean_ctor_set(v_reuseFailAlloc_2176_, 7, v_moreLinkLibs_2159_);
lean_ctor_set(v_reuseFailAlloc_2176_, 8, v_moreLinkArgs_2160_);
lean_ctor_set(v_reuseFailAlloc_2176_, 9, v_weakLinkArgs_2161_);
lean_ctor_set(v_reuseFailAlloc_2176_, 10, v_platformIndependent_2163_);
lean_ctor_set(v_reuseFailAlloc_2176_, 11, v_dynlibs_2164_);
lean_ctor_set(v_reuseFailAlloc_2176_, 12, v_plugins_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2176_, sizeof(void*)*13, v_buildType_2151_);
lean_ctor_set_uint8(v_reuseFailAlloc_2176_, sizeof(void*)*13 + 1, v_backend_2162_);
v___x_2174_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_unbox(v___x_2172_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*13 + 2, v___x_2175_);
lean_ctor_set_uint8(v___x_2174_, sizeof(void*)*13 + 3, v_allowNonModules_2167_);
return v___x_2174_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3(lean_object* v_x_2178_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = 0;
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3___boxed(lean_object* v_x_2180_){
_start:
{
uint8_t v_res_2181_; lean_object* v_r_2182_; 
v_res_2181_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3(v_x_2180_);
lean_dec_ref(v_x_2180_);
v_r_2182_ = lean_box(v_res_2181_);
return v_r_2182_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object* v_cfg_2194_){
_start:
{
uint8_t v_allowNonModules_2195_; 
v_allowNonModules_2195_ = lean_ctor_get_uint8(v_cfg_2194_, sizeof(void*)*13 + 3);
return v_allowNonModules_2195_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object* v_cfg_2196_){
_start:
{
uint8_t v_res_2197_; lean_object* v_r_2198_; 
v_res_2197_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2196_);
lean_dec_ref(v_cfg_2196_);
v_r_2198_ = lean_box(v_res_2197_);
return v_r_2198_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t v_val_2199_, lean_object* v_cfg_2200_){
_start:
{
uint8_t v_buildType_2201_; lean_object* v_leanOptions_2202_; lean_object* v_moreLeanArgs_2203_; lean_object* v_weakLeanArgs_2204_; lean_object* v_moreLeancArgs_2205_; lean_object* v_moreServerOptions_2206_; lean_object* v_weakLeancArgs_2207_; lean_object* v_moreLinkObjs_2208_; lean_object* v_moreLinkLibs_2209_; lean_object* v_moreLinkArgs_2210_; lean_object* v_weakLinkArgs_2211_; uint8_t v_backend_2212_; lean_object* v_platformIndependent_2213_; lean_object* v_dynlibs_2214_; lean_object* v_plugins_2215_; uint8_t v_requiresModuleSystem_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
v_buildType_2201_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*13);
v_leanOptions_2202_ = lean_ctor_get(v_cfg_2200_, 0);
v_moreLeanArgs_2203_ = lean_ctor_get(v_cfg_2200_, 1);
v_weakLeanArgs_2204_ = lean_ctor_get(v_cfg_2200_, 2);
v_moreLeancArgs_2205_ = lean_ctor_get(v_cfg_2200_, 3);
v_moreServerOptions_2206_ = lean_ctor_get(v_cfg_2200_, 4);
v_weakLeancArgs_2207_ = lean_ctor_get(v_cfg_2200_, 5);
v_moreLinkObjs_2208_ = lean_ctor_get(v_cfg_2200_, 6);
v_moreLinkLibs_2209_ = lean_ctor_get(v_cfg_2200_, 7);
v_moreLinkArgs_2210_ = lean_ctor_get(v_cfg_2200_, 8);
v_weakLinkArgs_2211_ = lean_ctor_get(v_cfg_2200_, 9);
v_backend_2212_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*13 + 1);
v_platformIndependent_2213_ = lean_ctor_get(v_cfg_2200_, 10);
v_dynlibs_2214_ = lean_ctor_get(v_cfg_2200_, 11);
v_plugins_2215_ = lean_ctor_get(v_cfg_2200_, 12);
v_requiresModuleSystem_2216_ = lean_ctor_get_uint8(v_cfg_2200_, sizeof(void*)*13 + 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_cfg_2200_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v_cfg_2200_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_plugins_2215_);
lean_inc(v_dynlibs_2214_);
lean_inc(v_platformIndependent_2213_);
lean_inc(v_weakLinkArgs_2211_);
lean_inc(v_moreLinkArgs_2210_);
lean_inc(v_moreLinkLibs_2209_);
lean_inc(v_moreLinkObjs_2208_);
lean_inc(v_weakLeancArgs_2207_);
lean_inc(v_moreServerOptions_2206_);
lean_inc(v_moreLeancArgs_2205_);
lean_inc(v_weakLeanArgs_2204_);
lean_inc(v_moreLeanArgs_2203_);
lean_inc(v_leanOptions_2202_);
lean_dec(v_cfg_2200_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_leanOptions_2202_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_moreLeanArgs_2203_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_weakLeanArgs_2204_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_moreLeancArgs_2205_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_moreServerOptions_2206_);
lean_ctor_set(v_reuseFailAlloc_2222_, 5, v_weakLeancArgs_2207_);
lean_ctor_set(v_reuseFailAlloc_2222_, 6, v_moreLinkObjs_2208_);
lean_ctor_set(v_reuseFailAlloc_2222_, 7, v_moreLinkLibs_2209_);
lean_ctor_set(v_reuseFailAlloc_2222_, 8, v_moreLinkArgs_2210_);
lean_ctor_set(v_reuseFailAlloc_2222_, 9, v_weakLinkArgs_2211_);
lean_ctor_set(v_reuseFailAlloc_2222_, 10, v_platformIndependent_2213_);
lean_ctor_set(v_reuseFailAlloc_2222_, 11, v_dynlibs_2214_);
lean_ctor_set(v_reuseFailAlloc_2222_, 12, v_plugins_2215_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13, v_buildType_2201_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 1, v_backend_2212_);
lean_ctor_set_uint8(v_reuseFailAlloc_2222_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_ctor_set_uint8(v___x_2221_, sizeof(void*)*13 + 3, v_val_2199_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object* v_val_2224_, lean_object* v_cfg_2225_){
_start:
{
uint8_t v_val_85__boxed_2226_; lean_object* v_res_2227_; 
v_val_85__boxed_2226_ = lean_unbox(v_val_2224_);
v_res_2227_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_85__boxed_2226_, v_cfg_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object* v_f_2228_, lean_object* v_cfg_2229_){
_start:
{
uint8_t v_buildType_2230_; lean_object* v_leanOptions_2231_; lean_object* v_moreLeanArgs_2232_; lean_object* v_weakLeanArgs_2233_; lean_object* v_moreLeancArgs_2234_; lean_object* v_moreServerOptions_2235_; lean_object* v_weakLeancArgs_2236_; lean_object* v_moreLinkObjs_2237_; lean_object* v_moreLinkLibs_2238_; lean_object* v_moreLinkArgs_2239_; lean_object* v_weakLinkArgs_2240_; uint8_t v_backend_2241_; lean_object* v_platformIndependent_2242_; lean_object* v_dynlibs_2243_; lean_object* v_plugins_2244_; uint8_t v_requiresModuleSystem_2245_; uint8_t v_allowNonModules_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2256_; 
v_buildType_2230_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*13);
v_leanOptions_2231_ = lean_ctor_get(v_cfg_2229_, 0);
v_moreLeanArgs_2232_ = lean_ctor_get(v_cfg_2229_, 1);
v_weakLeanArgs_2233_ = lean_ctor_get(v_cfg_2229_, 2);
v_moreLeancArgs_2234_ = lean_ctor_get(v_cfg_2229_, 3);
v_moreServerOptions_2235_ = lean_ctor_get(v_cfg_2229_, 4);
v_weakLeancArgs_2236_ = lean_ctor_get(v_cfg_2229_, 5);
v_moreLinkObjs_2237_ = lean_ctor_get(v_cfg_2229_, 6);
v_moreLinkLibs_2238_ = lean_ctor_get(v_cfg_2229_, 7);
v_moreLinkArgs_2239_ = lean_ctor_get(v_cfg_2229_, 8);
v_weakLinkArgs_2240_ = lean_ctor_get(v_cfg_2229_, 9);
v_backend_2241_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*13 + 1);
v_platformIndependent_2242_ = lean_ctor_get(v_cfg_2229_, 10);
v_dynlibs_2243_ = lean_ctor_get(v_cfg_2229_, 11);
v_plugins_2244_ = lean_ctor_get(v_cfg_2229_, 12);
v_requiresModuleSystem_2245_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*13 + 2);
v_allowNonModules_2246_ = lean_ctor_get_uint8(v_cfg_2229_, sizeof(void*)*13 + 3);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_cfg_2229_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2248_ = v_cfg_2229_;
v_isShared_2249_ = v_isSharedCheck_2256_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_plugins_2244_);
lean_inc(v_dynlibs_2243_);
lean_inc(v_platformIndependent_2242_);
lean_inc(v_weakLinkArgs_2240_);
lean_inc(v_moreLinkArgs_2239_);
lean_inc(v_moreLinkLibs_2238_);
lean_inc(v_moreLinkObjs_2237_);
lean_inc(v_weakLeancArgs_2236_);
lean_inc(v_moreServerOptions_2235_);
lean_inc(v_moreLeancArgs_2234_);
lean_inc(v_weakLeanArgs_2233_);
lean_inc(v_moreLeanArgs_2232_);
lean_inc(v_leanOptions_2231_);
lean_dec(v_cfg_2229_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2256_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2250_ = lean_box(v_allowNonModules_2246_);
v___x_2251_ = lean_apply_1(v_f_2228_, v___x_2250_);
if (v_isShared_2249_ == 0)
{
v___x_2253_ = v___x_2248_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_leanOptions_2231_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_moreLeanArgs_2232_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_weakLeanArgs_2233_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_moreLeancArgs_2234_);
lean_ctor_set(v_reuseFailAlloc_2255_, 4, v_moreServerOptions_2235_);
lean_ctor_set(v_reuseFailAlloc_2255_, 5, v_weakLeancArgs_2236_);
lean_ctor_set(v_reuseFailAlloc_2255_, 6, v_moreLinkObjs_2237_);
lean_ctor_set(v_reuseFailAlloc_2255_, 7, v_moreLinkLibs_2238_);
lean_ctor_set(v_reuseFailAlloc_2255_, 8, v_moreLinkArgs_2239_);
lean_ctor_set(v_reuseFailAlloc_2255_, 9, v_weakLinkArgs_2240_);
lean_ctor_set(v_reuseFailAlloc_2255_, 10, v_platformIndependent_2242_);
lean_ctor_set(v_reuseFailAlloc_2255_, 11, v_dynlibs_2243_);
lean_ctor_set(v_reuseFailAlloc_2255_, 12, v_plugins_2244_);
lean_ctor_set_uint8(v_reuseFailAlloc_2255_, sizeof(void*)*13, v_buildType_2230_);
lean_ctor_set_uint8(v_reuseFailAlloc_2255_, sizeof(void*)*13 + 1, v_backend_2241_);
lean_ctor_set_uint8(v_reuseFailAlloc_2255_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2245_);
v___x_2253_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_unbox(v___x_2251_);
lean_ctor_set_uint8(v___x_2253_, sizeof(void*)*13 + 3, v___x_2254_);
return v___x_2253_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2275_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2276_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2277_ = lean_array_push(v___x_2276_, v___x_2275_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2285_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2286_ = lean_array_push(v___x_2285_, v___x_2284_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2294_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2295_ = lean_array_push(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2303_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2304_ = lean_array_push(v___x_2303_, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2312_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2313_ = lean_array_push(v___x_2312_, v___x_2311_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2321_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2322_ = lean_array_push(v___x_2321_, v___x_2320_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2329_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2330_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2331_ = lean_array_push(v___x_2330_, v___x_2329_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2339_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2340_ = lean_array_push(v___x_2339_, v___x_2338_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2348_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2349_ = lean_array_push(v___x_2348_, v___x_2347_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2357_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2358_ = lean_array_push(v___x_2357_, v___x_2356_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2366_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2367_ = lean_array_push(v___x_2366_, v___x_2365_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2375_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2376_ = lean_array_push(v___x_2375_, v___x_2374_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2384_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2385_ = lean_array_push(v___x_2384_, v___x_2383_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2393_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2394_ = lean_array_push(v___x_2393_, v___x_2392_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2402_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2403_ = lean_array_push(v___x_2402_, v___x_2401_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__47));
v___x_2411_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
v___x_2412_ = lean_array_push(v___x_2411_, v___x_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__51(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__50));
v___x_2420_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__48, &l_Lake_LeanConfig___fields___closed__48_once, _init_l_Lake_LeanConfig___fields___closed__48);
v___x_2421_ = lean_array_push(v___x_2420_, v___x_2419_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__51, &l_Lake_LeanConfig___fields___closed__51_once, _init_l_Lake_LeanConfig___fields___closed__51);
return v___x_2422_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lake_LeanConfig___fields;
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2424_, lean_object* v_x2_2425_){
_start:
{
lean_object* v_name_2426_; lean_object* v___x_2427_; 
v_name_2426_ = lean_ctor_get(v_x2_2425_, 0);
lean_inc(v_name_2426_);
v___x_2427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2426_, v_x2_2425_, v_x1_2424_);
return v___x_2427_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = l_Lake_LeanConfig___fields;
v___x_2429_ = lean_array_get_size(v___x_2428_);
return v___x_2429_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2449_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2450_ = lean_unsigned_to_nat(0u);
v___x_2451_ = lean_nat_dec_lt(v___x_2450_, v___x_2449_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2452_ = lean_unsigned_to_nat(0u);
v___x_2453_ = lean_box(1);
v___x_2454_ = l_Lake_LeanConfig___fields;
v___x_2455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
lean_ctor_set(v___x_2455_, 1, v___x_2453_);
lean_ctor_set(v___x_2455_, 2, v___x_2452_);
return v___x_2455_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2458_ = lean_nat_dec_le(v___x_2457_, v___x_2457_);
return v___x_2458_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2459_; size_t v___x_2460_; 
v___x_2459_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2460_ = lean_usize_of_nat(v___x_2459_);
return v___x_2460_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; lean_object* v___x_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2461_ = lean_box(1);
v___x_2462_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2463_ = ((size_t)0ULL);
v___x_2464_ = l_Lake_LeanConfig___fields;
v___f_2465_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2466_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2466_, v___f_2465_, v___x_2464_, v___x_2463_, v___x_2462_, v___x_2461_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2468_ = lean_unsigned_to_nat(0u);
v___x_2469_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2470_ = l_Lake_LeanConfig___fields;
v___x_2471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2471_, 0, v___x_2470_);
lean_ctor_set(v___x_2471_, 1, v___x_2469_);
lean_ctor_set(v___x_2471_, 2, v___x_2468_);
return v___x_2471_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2473_;
}
else
{
uint8_t v___x_2474_; 
v___x_2474_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2474_ == 0)
{
if (v___x_2472_ == 0)
{
lean_object* v___x_2475_; 
v___x_2475_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2476_;
}
}
else
{
lean_object* v___x_2477_; 
v___x_2477_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2477_;
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

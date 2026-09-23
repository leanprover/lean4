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
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___redArg(){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = ((lean_object*)(l_Lake_BuildType_leanArgs___redArg___closed__0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___redArg___boxed(lean_object* v___dummy_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lake_BuildType_leanArgs___redArg();
return v_res_501_;
}
}
static lean_object* _init_l_Lake_BuildType_leanArgs___closed__0(void){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lake_BuildType_leanArgs___redArg();
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs(uint8_t v_t_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lake_BuildType_leanArgs___closed__0, &l_Lake_BuildType_leanArgs___closed__0_once, _init_l_Lake_BuildType_leanArgs___closed__0);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___boxed(lean_object* v_t_505_){
_start:
{
uint8_t v_t_boxed_506_; lean_object* v_res_507_; 
v_t_boxed_506_ = lean_unbox(v_t_505_);
v_res_507_ = l_Lake_BuildType_leanArgs(v_t_boxed_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
lean_object* v___x_526_; 
v___x_526_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1));
return v___x_526_;
}
else
{
lean_object* v_val_527_; lean_object* v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_val_527_ = lean_ctor_get(v_x_524_, 0);
v___x_528_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3));
v___x_529_ = lean_unbox(v_val_527_);
v___x_530_ = l_Bool_repr___redArg(v___x_529_);
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_528_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Repr_addAppParen(v___x_531_, v_x_525_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_533_, v_x_534_);
lean_dec(v_x_534_);
lean_dec(v_x_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = lean_nat_to_int(v_a_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object* v___y_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = l_String_quote(v___y_538_);
v___x_540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
lean_dec(v_x_541_);
return v_x_542_;
}
else
{
lean_object* v_head_544_; lean_object* v_tail_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_556_; 
v_head_544_ = lean_ctor_get(v_x_543_, 0);
v_tail_545_ = lean_ctor_get(v_x_543_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_556_ == 0)
{
v___x_547_ = v_x_543_;
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_tail_545_);
lean_inc(v_head_544_);
lean_dec(v_x_543_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_556_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
lean_inc(v_x_541_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 5);
lean_ctor_set(v___x_547_, 1, v_x_541_);
lean_ctor_set(v___x_547_, 0, v_x_542_);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_x_542_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_x_541_);
v___x_550_ = v_reuseFailAlloc_555_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_551_ = l_String_quote(v_head_544_);
v___x_552_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_552_, 0, v___x_551_);
v___x_553_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_550_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v_x_542_ = v___x_553_;
v_x_543_ = v_tail_545_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
lean_dec(v_x_557_);
return v_x_558_;
}
else
{
lean_object* v_head_560_; lean_object* v_tail_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_572_; 
v_head_560_ = lean_ctor_get(v_x_559_, 0);
v_tail_561_ = lean_ctor_get(v_x_559_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_559_);
if (v_isSharedCheck_572_ == 0)
{
v___x_563_ = v_x_559_;
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_tail_561_);
lean_inc(v_head_560_);
lean_dec(v_x_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_572_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
lean_inc(v_x_557_);
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 5);
lean_ctor_set(v___x_563_, 1, v_x_557_);
lean_ctor_set(v___x_563_, 0, v_x_558_);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_x_558_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_x_557_);
v___x_566_ = v_reuseFailAlloc_571_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_567_ = l_String_quote(v_head_560_);
v___x_568_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
v___x_569_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_557_, v___x_569_, v_tail_561_);
return v___x_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object* v_x_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
lean_object* v___x_575_; 
lean_dec(v_x_574_);
v___x_575_ = lean_box(0);
return v___x_575_;
}
else
{
lean_object* v_tail_576_; 
v_tail_576_ = lean_ctor_get(v_x_573_, 1);
if (lean_obj_tag(v_tail_576_) == 0)
{
lean_object* v_head_577_; lean_object* v___x_578_; 
lean_dec(v_x_574_);
v_head_577_ = lean_ctor_get(v_x_573_, 0);
lean_inc(v_head_577_);
lean_dec_ref_known(v_x_573_, 2);
v___x_578_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_577_);
return v___x_578_;
}
else
{
lean_object* v_head_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
lean_inc(v_tail_576_);
v_head_579_ = lean_ctor_get(v_x_573_, 0);
lean_inc(v_head_579_);
lean_dec_ref_known(v_x_573_, 2);
v___x_580_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_579_);
v___x_581_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_574_, v___x_580_, v_tail_576_);
return v___x_581_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0));
v___x_591_ = lean_string_length(v___x_590_);
return v___x_591_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_592_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5);
v___x_593_ = lean_nat_to_int(v___x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object* v_xs_601_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_602_ = lean_array_get_size(v_xs_601_);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_nat_dec_eq(v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_605_ = lean_array_to_list(v_xs_601_);
v___x_606_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_607_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_605_, v___x_606_);
v___x_608_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_609_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_610_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_607_);
v___x_611_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_612_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_608_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = l_Std_Format_fill(v___x_613_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
lean_dec_ref(v_xs_601_);
v___x_615_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object* v___y_616_){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = l_Lake_Target_repr___redArg(v___y_616_, v___x_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object* v_x_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
lean_dec(v_x_619_);
return v_x_620_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_634_; 
v_head_622_ = lean_ctor_get(v_x_621_, 0);
v_tail_623_ = lean_ctor_get(v_x_621_, 1);
v_isSharedCheck_634_ = !lean_is_exclusive(v_x_621_);
if (v_isSharedCheck_634_ == 0)
{
v___x_625_ = v_x_621_;
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tail_623_);
lean_inc(v_head_622_);
lean_dec(v_x_621_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_634_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
lean_inc(v_x_619_);
if (v_isShared_626_ == 0)
{
lean_ctor_set_tag(v___x_625_, 5);
lean_ctor_set(v___x_625_, 1, v_x_619_);
lean_ctor_set(v___x_625_, 0, v_x_620_);
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_x_620_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_x_619_);
v___x_628_ = v_reuseFailAlloc_633_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = l_Lake_Target_repr___redArg(v_head_622_, v___x_629_);
v___x_631_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_628_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v_x_620_ = v___x_631_;
v_x_621_ = v_tail_623_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_dec(v_x_635_);
return v_x_636_;
}
else
{
lean_object* v_head_638_; lean_object* v_tail_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_650_; 
v_head_638_ = lean_ctor_get(v_x_637_, 0);
v_tail_639_ = lean_ctor_get(v_x_637_, 1);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_650_ == 0)
{
v___x_641_ = v_x_637_;
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_tail_639_);
lean_inc(v_head_638_);
lean_dec(v_x_637_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
lean_inc(v_x_635_);
if (v_isShared_642_ == 0)
{
lean_ctor_set_tag(v___x_641_, 5);
lean_ctor_set(v___x_641_, 1, v_x_635_);
lean_ctor_set(v___x_641_, 0, v_x_636_);
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_x_636_);
lean_ctor_set(v_reuseFailAlloc_649_, 1, v_x_635_);
v___x_644_ = v_reuseFailAlloc_649_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_Lake_Target_repr___redArg(v_head_638_, v___x_645_);
v___x_647_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_644_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v___x_648_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_635_, v___x_647_, v_tail_639_);
return v___x_648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v___x_653_; 
lean_dec(v_x_652_);
v___x_653_ = lean_box(0);
return v___x_653_;
}
else
{
lean_object* v_tail_654_; 
v_tail_654_ = lean_ctor_get(v_x_651_, 1);
if (lean_obj_tag(v_tail_654_) == 0)
{
lean_object* v_head_655_; lean_object* v___x_656_; 
lean_dec(v_x_652_);
v_head_655_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_head_655_);
lean_dec_ref_known(v_x_651_, 2);
v___x_656_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_655_);
return v___x_656_;
}
else
{
lean_object* v_head_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_inc(v_tail_654_);
v_head_657_ = lean_ctor_get(v_x_651_, 0);
lean_inc(v_head_657_);
lean_dec_ref_known(v_x_651_, 2);
v___x_658_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_657_);
v___x_659_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_652_, v___x_658_, v_tail_654_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object* v_xs_660_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_661_ = lean_array_get_size(v_xs_660_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_nat_dec_eq(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_664_ = lean_array_to_list(v_xs_660_);
v___x_665_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_666_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_664_, v___x_665_);
v___x_667_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_668_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_669_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
lean_ctor_set(v___x_669_, 1, v___x_666_);
v___x_670_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_671_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_667_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Std_Format_fill(v___x_672_);
return v___x_673_;
}
else
{
lean_object* v___x_674_; 
lean_dec_ref(v_xs_660_);
v___x_674_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_675_, lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_dec(v_x_675_);
return v_x_676_;
}
else
{
lean_object* v_head_678_; lean_object* v_tail_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_689_; 
v_head_678_ = lean_ctor_get(v_x_677_, 0);
v_tail_679_ = lean_ctor_get(v_x_677_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_x_677_);
if (v_isSharedCheck_689_ == 0)
{
v___x_681_ = v_x_677_;
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_tail_679_);
lean_inc(v_head_678_);
lean_dec(v_x_677_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_689_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
lean_inc(v_x_675_);
if (v_isShared_682_ == 0)
{
lean_ctor_set_tag(v___x_681_, 5);
lean_ctor_set(v___x_681_, 1, v_x_675_);
lean_ctor_set(v___x_681_, 0, v_x_676_);
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_x_676_);
lean_ctor_set(v_reuseFailAlloc_688_, 1, v_x_675_);
v___x_684_ = v_reuseFailAlloc_688_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_Lean_instReprLeanOption_repr___redArg(v_head_678_);
v___x_686_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_684_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v_x_676_ = v___x_686_;
v_x_677_ = v_tail_679_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_x_692_){
_start:
{
if (lean_obj_tag(v_x_692_) == 0)
{
lean_dec(v_x_690_);
return v_x_691_;
}
else
{
lean_object* v_head_693_; lean_object* v_tail_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_704_; 
v_head_693_ = lean_ctor_get(v_x_692_, 0);
v_tail_694_ = lean_ctor_get(v_x_692_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_x_692_);
if (v_isSharedCheck_704_ == 0)
{
v___x_696_ = v_x_692_;
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_tail_694_);
lean_inc(v_head_693_);
lean_dec(v_x_692_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_704_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
lean_inc(v_x_690_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 5);
lean_ctor_set(v___x_696_, 1, v_x_690_);
lean_ctor_set(v___x_696_, 0, v_x_691_);
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_x_691_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_x_690_);
v___x_699_ = v_reuseFailAlloc_703_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_700_ = l_Lean_instReprLeanOption_repr___redArg(v_head_693_);
v___x_701_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v___x_702_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_690_, v___x_701_, v_tail_694_);
return v___x_702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
lean_object* v___x_707_; 
lean_dec(v_x_706_);
v___x_707_ = lean_box(0);
return v___x_707_;
}
else
{
lean_object* v_tail_708_; 
v_tail_708_ = lean_ctor_get(v_x_705_, 1);
if (lean_obj_tag(v_tail_708_) == 0)
{
lean_object* v_head_709_; lean_object* v___x_710_; 
lean_dec(v_x_706_);
v_head_709_ = lean_ctor_get(v_x_705_, 0);
lean_inc(v_head_709_);
lean_dec_ref_known(v_x_705_, 2);
v___x_710_ = l_Lean_instReprLeanOption_repr___redArg(v_head_709_);
return v___x_710_;
}
else
{
lean_object* v_head_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_inc(v_tail_708_);
v_head_711_ = lean_ctor_get(v_x_705_, 0);
lean_inc(v_head_711_);
lean_dec_ref_known(v_x_705_, 2);
v___x_712_ = l_Lean_instReprLeanOption_repr___redArg(v_head_711_);
v___x_713_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_706_, v___x_712_, v_tail_708_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object* v_xs_714_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = lean_array_get_size(v_xs_714_);
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = lean_nat_dec_eq(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_718_ = lean_array_to_list(v_xs_714_);
v___x_719_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_720_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_718_, v___x_719_);
v___x_721_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_722_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_723_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
lean_ctor_set(v___x_723_, 1, v___x_720_);
v___x_724_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_725_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_723_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
v___x_726_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_721_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
v___x_727_ = l_Std_Format_fill(v___x_726_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; 
lean_dec_ref(v_xs_714_);
v___x_728_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_728_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_731_) == 0)
{
lean_dec(v_x_729_);
return v_x_730_;
}
else
{
lean_object* v_head_732_; lean_object* v_tail_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_744_; 
v_head_732_ = lean_ctor_get(v_x_731_, 0);
v_tail_733_ = lean_ctor_get(v_x_731_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_x_731_);
if (v_isSharedCheck_744_ == 0)
{
v___x_735_ = v_x_731_;
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_tail_733_);
lean_inc(v_head_732_);
lean_dec(v_x_731_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_744_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
lean_inc(v_x_729_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 5);
lean_ctor_set(v___x_735_, 1, v_x_729_);
lean_ctor_set(v___x_735_, 0, v_x_730_);
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_x_730_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v_x_729_);
v___x_738_ = v_reuseFailAlloc_743_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = l_Lake_Target_repr___redArg(v_head_732_, v___x_739_);
v___x_741_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_738_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v_x_730_ = v___x_741_;
v_x_731_ = v_tail_733_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_){
_start:
{
if (lean_obj_tag(v_x_747_) == 0)
{
lean_dec(v_x_745_);
return v_x_746_;
}
else
{
lean_object* v_head_748_; lean_object* v_tail_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_760_; 
v_head_748_ = lean_ctor_get(v_x_747_, 0);
v_tail_749_ = lean_ctor_get(v_x_747_, 1);
v_isSharedCheck_760_ = !lean_is_exclusive(v_x_747_);
if (v_isSharedCheck_760_ == 0)
{
v___x_751_ = v_x_747_;
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_tail_749_);
lean_inc(v_head_748_);
lean_dec(v_x_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
lean_inc(v_x_745_);
if (v_isShared_752_ == 0)
{
lean_ctor_set_tag(v___x_751_, 5);
lean_ctor_set(v___x_751_, 1, v_x_745_);
lean_ctor_set(v___x_751_, 0, v_x_746_);
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_x_746_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_x_745_);
v___x_754_ = v_reuseFailAlloc_759_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_unsigned_to_nat(0u);
v___x_756_ = l_Lake_Target_repr___redArg(v_head_748_, v___x_755_);
v___x_757_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_754_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_745_, v___x_757_, v_tail_749_);
return v___x_758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v___x_763_; 
lean_dec(v_x_762_);
v___x_763_ = lean_box(0);
return v___x_763_;
}
else
{
lean_object* v_tail_764_; 
v_tail_764_ = lean_ctor_get(v_x_761_, 1);
if (lean_obj_tag(v_tail_764_) == 0)
{
lean_object* v_head_765_; lean_object* v___x_766_; 
lean_dec(v_x_762_);
v_head_765_ = lean_ctor_get(v_x_761_, 0);
lean_inc(v_head_765_);
lean_dec_ref_known(v_x_761_, 2);
v___x_766_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_765_);
return v___x_766_;
}
else
{
lean_object* v_head_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
lean_inc(v_tail_764_);
v_head_767_ = lean_ctor_get(v_x_761_, 0);
lean_inc(v_head_767_);
lean_dec_ref_known(v_x_761_, 2);
v___x_768_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_767_);
v___x_769_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_762_, v___x_768_, v_tail_764_);
return v___x_769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object* v_xs_770_){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_771_ = lean_array_get_size(v_xs_770_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_nat_dec_eq(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_774_ = lean_array_to_list(v_xs_770_);
v___x_775_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_776_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_774_, v___x_775_);
v___x_777_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_778_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_779_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v___x_776_);
v___x_780_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_781_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
v___x_782_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_777_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = l_Std_Format_fill(v___x_782_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; 
lean_dec_ref(v_xs_770_);
v___x_784_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_784_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(13u);
v___x_799_ = lean_nat_to_int(v___x_798_);
return v___x_799_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_unsigned_to_nat(15u);
v___x_804_ = lean_nat_to_int(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_unsigned_to_nat(16u);
v___x_809_ = lean_nat_to_int(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = lean_unsigned_to_nat(17u);
v___x_817_ = lean_nat_to_int(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(21u);
v___x_822_ = lean_nat_to_int(v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_unsigned_to_nat(11u);
v___x_842_ = lean_nat_to_int(v___x_841_);
return v___x_842_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(23u);
v___x_847_ = lean_nat_to_int(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(24u);
v___x_861_ = lean_nat_to_int(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_unsigned_to_nat(19u);
v___x_866_ = lean_nat_to_int(v___x_865_);
return v___x_866_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_868_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_869_ = lean_string_length(v___x_868_);
return v___x_869_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__51, &l_Lake_instReprLeanConfig_repr___redArg___closed__51_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51);
v___x_871_ = lean_nat_to_int(v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_876_){
_start:
{
uint8_t v_buildType_877_; lean_object* v_leanOptions_878_; lean_object* v_moreLeanArgs_879_; lean_object* v_weakLeanArgs_880_; lean_object* v_moreLeancArgs_881_; lean_object* v_moreServerOptions_882_; lean_object* v_weakLeancArgs_883_; lean_object* v_moreLinkObjs_884_; lean_object* v_moreLinkLibs_885_; lean_object* v_moreLinkArgs_886_; lean_object* v_weakLinkArgs_887_; uint8_t v_backend_888_; lean_object* v_platformIndependent_889_; uint8_t v_precompileImports_890_; lean_object* v_dynlibs_891_; lean_object* v_plugins_892_; uint8_t v_requiresModuleSystem_893_; uint8_t v_allowNonModules_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_buildType_877_ = lean_ctor_get_uint8(v_x_876_, sizeof(void*)*13);
v_leanOptions_878_ = lean_ctor_get(v_x_876_, 0);
lean_inc_ref(v_leanOptions_878_);
v_moreLeanArgs_879_ = lean_ctor_get(v_x_876_, 1);
lean_inc_ref(v_moreLeanArgs_879_);
v_weakLeanArgs_880_ = lean_ctor_get(v_x_876_, 2);
lean_inc_ref(v_weakLeanArgs_880_);
v_moreLeancArgs_881_ = lean_ctor_get(v_x_876_, 3);
lean_inc_ref(v_moreLeancArgs_881_);
v_moreServerOptions_882_ = lean_ctor_get(v_x_876_, 4);
lean_inc_ref(v_moreServerOptions_882_);
v_weakLeancArgs_883_ = lean_ctor_get(v_x_876_, 5);
lean_inc_ref(v_weakLeancArgs_883_);
v_moreLinkObjs_884_ = lean_ctor_get(v_x_876_, 6);
lean_inc_ref(v_moreLinkObjs_884_);
v_moreLinkLibs_885_ = lean_ctor_get(v_x_876_, 7);
lean_inc_ref(v_moreLinkLibs_885_);
v_moreLinkArgs_886_ = lean_ctor_get(v_x_876_, 8);
lean_inc_ref(v_moreLinkArgs_886_);
v_weakLinkArgs_887_ = lean_ctor_get(v_x_876_, 9);
lean_inc_ref(v_weakLinkArgs_887_);
v_backend_888_ = lean_ctor_get_uint8(v_x_876_, sizeof(void*)*13 + 1);
v_platformIndependent_889_ = lean_ctor_get(v_x_876_, 10);
lean_inc(v_platformIndependent_889_);
v_precompileImports_890_ = lean_ctor_get_uint8(v_x_876_, sizeof(void*)*13 + 2);
v_dynlibs_891_ = lean_ctor_get(v_x_876_, 11);
lean_inc_ref(v_dynlibs_891_);
v_plugins_892_ = lean_ctor_get(v_x_876_, 12);
lean_inc_ref(v_plugins_892_);
v_requiresModuleSystem_893_ = lean_ctor_get_uint8(v_x_876_, sizeof(void*)*13 + 3);
v_allowNonModules_894_ = lean_ctor_get_uint8(v_x_876_, sizeof(void*)*13 + 4);
lean_dec_ref(v_x_876_);
v___x_895_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_896_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_897_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = l_Lake_instReprBuildType_repr(v_buildType_877_, v___x_898_);
v___x_900_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_897_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = 0;
v___x_902_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set_uint8(v___x_902_, sizeof(void*)*1, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_896_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2));
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_903_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = lean_box(1);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_905_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__9));
v___x_909_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
lean_ctor_set(v___x_910_, 1, v___x_895_);
v___x_911_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__10, &l_Lake_instReprLeanConfig_repr___redArg___closed__10_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10);
v___x_912_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_878_);
v___x_913_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*1, v___x_901_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_910_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v___x_904_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_906_);
v___x_918_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__12));
v___x_919_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set(v___x_920_, 1, v___x_895_);
v___x_921_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__13, &l_Lake_instReprLeanConfig_repr___redArg___closed__13_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13);
v___x_922_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_879_);
v___x_923_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_921_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set_uint8(v___x_924_, sizeof(void*)*1, v___x_901_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_920_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_904_);
v___x_927_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_906_);
v___x_928_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__15));
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_895_);
v___x_931_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_880_);
v___x_932_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_921_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*1, v___x_901_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_930_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v___x_904_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_906_);
v___x_937_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__17));
v___x_938_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
lean_ctor_set(v___x_939_, 1, v___x_895_);
v___x_940_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__18, &l_Lake_instReprLeanConfig_repr___redArg___closed__18_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18);
v___x_941_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_881_);
v___x_942_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set_uint8(v___x_943_, sizeof(void*)*1, v___x_901_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_939_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_904_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_906_);
v___x_947_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__20));
v___x_948_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set(v___x_949_, 1, v___x_895_);
v___x_950_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__21, &l_Lake_instReprLeanConfig_repr___redArg___closed__21_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21);
v___x_951_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_882_);
v___x_952_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_953_, 0, v___x_952_);
lean_ctor_set_uint8(v___x_953_, sizeof(void*)*1, v___x_901_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_949_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_904_);
v___x_956_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_906_);
v___x_957_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__23));
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_895_);
v___x_960_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_883_);
v___x_961_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_940_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set_uint8(v___x_962_, sizeof(void*)*1, v___x_901_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_904_);
v___x_965_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_906_);
v___x_966_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__25));
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_895_);
v___x_969_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_884_);
v___x_970_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_921_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_971_, 0, v___x_970_);
lean_ctor_set_uint8(v___x_971_, sizeof(void*)*1, v___x_901_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_968_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_904_);
v___x_974_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_906_);
v___x_975_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__27));
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_895_);
v___x_978_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_885_);
v___x_979_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_921_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
v___x_980_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*1, v___x_901_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_977_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_904_);
v___x_983_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_906_);
v___x_984_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__29));
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_983_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_895_);
v___x_987_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_886_);
v___x_988_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_921_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set_uint8(v___x_989_, sizeof(void*)*1, v___x_901_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_986_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_904_);
v___x_992_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v___x_906_);
v___x_993_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__31));
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_895_);
v___x_996_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_887_);
v___x_997_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_921_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set_uint8(v___x_998_, sizeof(void*)*1, v___x_901_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_995_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v___x_904_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_906_);
v___x_1002_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__33));
v___x_1003_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
lean_ctor_set(v___x_1004_, 1, v___x_895_);
v___x_1005_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__34, &l_Lake_instReprLeanConfig_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34);
v___x_1006_ = l_Lake_instReprBackend_repr(v_backend_888_, v___x_898_);
v___x_1007_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set_uint8(v___x_1008_, sizeof(void*)*1, v___x_901_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1004_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_904_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_906_);
v___x_1012_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__36));
v___x_1013_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1011_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set(v___x_1014_, 1, v___x_895_);
v___x_1015_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__37, &l_Lake_instReprLeanConfig_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37);
v___x_1016_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_889_, v___x_898_);
lean_dec(v_platformIndependent_889_);
v___x_1017_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set_uint8(v___x_1018_, sizeof(void*)*1, v___x_901_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1014_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_904_);
v___x_1021_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v___x_906_);
v___x_1022_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__39));
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_895_);
v___x_1025_ = l_Bool_repr___redArg(v_precompileImports_890_);
v___x_1026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_950_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set_uint8(v___x_1027_, sizeof(void*)*1, v___x_901_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1024_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_904_);
v___x_1030_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_906_);
v___x_1031_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__41));
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1030_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_895_);
v___x_1034_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_891_);
v___x_1035_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1005_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set_uint8(v___x_1036_, sizeof(void*)*1, v___x_901_);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1033_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_904_);
v___x_1039_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_906_);
v___x_1040_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__43));
v___x_1041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_895_);
v___x_1043_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_892_);
v___x_1044_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1005_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set_uint8(v___x_1045_, sizeof(void*)*1, v___x_901_);
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1042_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v___x_904_);
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___x_906_);
v___x_1049_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__45));
v___x_1050_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v___x_895_);
v___x_1052_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__46, &l_Lake_instReprLeanConfig_repr___redArg___closed__46_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46);
v___x_1053_ = l_Bool_repr___redArg(v_requiresModuleSystem_893_);
v___x_1054_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*1, v___x_901_);
v___x_1056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1051_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_904_);
v___x_1058_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_906_);
v___x_1059_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__48));
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_895_);
v___x_1062_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__49, &l_Lake_instReprLeanConfig_repr___redArg___closed__49_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49);
v___x_1063_ = l_Bool_repr___redArg(v_allowNonModules_894_);
v___x_1064_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*1, v___x_901_);
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1061_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__52, &l_Lake_instReprLeanConfig_repr___redArg___closed__52_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52);
v___x_1068_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__53));
v___x_1069_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v___x_1066_);
v___x_1070_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__54));
v___x_1071_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1067_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set_uint8(v___x_1073_, sizeof(void*)*1, v___x_901_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1074_, lean_object* v_prec_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1077_, lean_object* v_prec_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lake_instReprLeanConfig_repr(v_x_1077_, v_prec_1078_);
lean_dec(v_prec_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1082_){
_start:
{
uint8_t v_buildType_1083_; 
v_buildType_1083_ = lean_ctor_get_uint8(v_cfg_1082_, sizeof(void*)*13);
return v_buildType_1083_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1084_);
lean_dec_ref(v_cfg_1084_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1087_, lean_object* v_cfg_1088_){
_start:
{
lean_object* v_leanOptions_1089_; lean_object* v_moreLeanArgs_1090_; lean_object* v_weakLeanArgs_1091_; lean_object* v_moreLeancArgs_1092_; lean_object* v_moreServerOptions_1093_; lean_object* v_weakLeancArgs_1094_; lean_object* v_moreLinkObjs_1095_; lean_object* v_moreLinkLibs_1096_; lean_object* v_moreLinkArgs_1097_; lean_object* v_weakLinkArgs_1098_; uint8_t v_backend_1099_; lean_object* v_platformIndependent_1100_; uint8_t v_precompileImports_1101_; lean_object* v_dynlibs_1102_; lean_object* v_plugins_1103_; uint8_t v_requiresModuleSystem_1104_; uint8_t v_allowNonModules_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
v_leanOptions_1089_ = lean_ctor_get(v_cfg_1088_, 0);
v_moreLeanArgs_1090_ = lean_ctor_get(v_cfg_1088_, 1);
v_weakLeanArgs_1091_ = lean_ctor_get(v_cfg_1088_, 2);
v_moreLeancArgs_1092_ = lean_ctor_get(v_cfg_1088_, 3);
v_moreServerOptions_1093_ = lean_ctor_get(v_cfg_1088_, 4);
v_weakLeancArgs_1094_ = lean_ctor_get(v_cfg_1088_, 5);
v_moreLinkObjs_1095_ = lean_ctor_get(v_cfg_1088_, 6);
v_moreLinkLibs_1096_ = lean_ctor_get(v_cfg_1088_, 7);
v_moreLinkArgs_1097_ = lean_ctor_get(v_cfg_1088_, 8);
v_weakLinkArgs_1098_ = lean_ctor_get(v_cfg_1088_, 9);
v_backend_1099_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*13 + 1);
v_platformIndependent_1100_ = lean_ctor_get(v_cfg_1088_, 10);
v_precompileImports_1101_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*13 + 2);
v_dynlibs_1102_ = lean_ctor_get(v_cfg_1088_, 11);
v_plugins_1103_ = lean_ctor_get(v_cfg_1088_, 12);
v_requiresModuleSystem_1104_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*13 + 3);
v_allowNonModules_1105_ = lean_ctor_get_uint8(v_cfg_1088_, sizeof(void*)*13 + 4);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_cfg_1088_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v_cfg_1088_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_plugins_1103_);
lean_inc(v_dynlibs_1102_);
lean_inc(v_platformIndependent_1100_);
lean_inc(v_weakLinkArgs_1098_);
lean_inc(v_moreLinkArgs_1097_);
lean_inc(v_moreLinkLibs_1096_);
lean_inc(v_moreLinkObjs_1095_);
lean_inc(v_weakLeancArgs_1094_);
lean_inc(v_moreServerOptions_1093_);
lean_inc(v_moreLeancArgs_1092_);
lean_inc(v_weakLeanArgs_1091_);
lean_inc(v_moreLeanArgs_1090_);
lean_inc(v_leanOptions_1089_);
lean_dec(v_cfg_1088_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_leanOptions_1089_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_moreLeanArgs_1090_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v_weakLeanArgs_1091_);
lean_ctor_set(v_reuseFailAlloc_1111_, 3, v_moreLeancArgs_1092_);
lean_ctor_set(v_reuseFailAlloc_1111_, 4, v_moreServerOptions_1093_);
lean_ctor_set(v_reuseFailAlloc_1111_, 5, v_weakLeancArgs_1094_);
lean_ctor_set(v_reuseFailAlloc_1111_, 6, v_moreLinkObjs_1095_);
lean_ctor_set(v_reuseFailAlloc_1111_, 7, v_moreLinkLibs_1096_);
lean_ctor_set(v_reuseFailAlloc_1111_, 8, v_moreLinkArgs_1097_);
lean_ctor_set(v_reuseFailAlloc_1111_, 9, v_weakLinkArgs_1098_);
lean_ctor_set(v_reuseFailAlloc_1111_, 10, v_platformIndependent_1100_);
lean_ctor_set(v_reuseFailAlloc_1111_, 11, v_dynlibs_1102_);
lean_ctor_set(v_reuseFailAlloc_1111_, 12, v_plugins_1103_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*13 + 1, v_backend_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*13 + 2, v_precompileImports_1101_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1104_);
lean_ctor_set_uint8(v_reuseFailAlloc_1111_, sizeof(void*)*13 + 4, v_allowNonModules_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_ctor_set_uint8(v___x_1110_, sizeof(void*)*13, v_val_1087_);
return v___x_1110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1113_, lean_object* v_cfg_1114_){
_start:
{
uint8_t v_val_88__boxed_1115_; lean_object* v_res_1116_; 
v_val_88__boxed_1115_ = lean_unbox(v_val_1113_);
v_res_1116_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_88__boxed_1115_, v_cfg_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1117_, lean_object* v_cfg_1118_){
_start:
{
uint8_t v_buildType_1119_; lean_object* v_leanOptions_1120_; lean_object* v_moreLeanArgs_1121_; lean_object* v_weakLeanArgs_1122_; lean_object* v_moreLeancArgs_1123_; lean_object* v_moreServerOptions_1124_; lean_object* v_weakLeancArgs_1125_; lean_object* v_moreLinkObjs_1126_; lean_object* v_moreLinkLibs_1127_; lean_object* v_moreLinkArgs_1128_; lean_object* v_weakLinkArgs_1129_; uint8_t v_backend_1130_; lean_object* v_platformIndependent_1131_; uint8_t v_precompileImports_1132_; lean_object* v_dynlibs_1133_; lean_object* v_plugins_1134_; uint8_t v_requiresModuleSystem_1135_; uint8_t v_allowNonModules_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1146_; 
v_buildType_1119_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13);
v_leanOptions_1120_ = lean_ctor_get(v_cfg_1118_, 0);
v_moreLeanArgs_1121_ = lean_ctor_get(v_cfg_1118_, 1);
v_weakLeanArgs_1122_ = lean_ctor_get(v_cfg_1118_, 2);
v_moreLeancArgs_1123_ = lean_ctor_get(v_cfg_1118_, 3);
v_moreServerOptions_1124_ = lean_ctor_get(v_cfg_1118_, 4);
v_weakLeancArgs_1125_ = lean_ctor_get(v_cfg_1118_, 5);
v_moreLinkObjs_1126_ = lean_ctor_get(v_cfg_1118_, 6);
v_moreLinkLibs_1127_ = lean_ctor_get(v_cfg_1118_, 7);
v_moreLinkArgs_1128_ = lean_ctor_get(v_cfg_1118_, 8);
v_weakLinkArgs_1129_ = lean_ctor_get(v_cfg_1118_, 9);
v_backend_1130_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 1);
v_platformIndependent_1131_ = lean_ctor_get(v_cfg_1118_, 10);
v_precompileImports_1132_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 2);
v_dynlibs_1133_ = lean_ctor_get(v_cfg_1118_, 11);
v_plugins_1134_ = lean_ctor_get(v_cfg_1118_, 12);
v_requiresModuleSystem_1135_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 3);
v_allowNonModules_1136_ = lean_ctor_get_uint8(v_cfg_1118_, sizeof(void*)*13 + 4);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_cfg_1118_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1138_ = v_cfg_1118_;
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_plugins_1134_);
lean_inc(v_dynlibs_1133_);
lean_inc(v_platformIndependent_1131_);
lean_inc(v_weakLinkArgs_1129_);
lean_inc(v_moreLinkArgs_1128_);
lean_inc(v_moreLinkLibs_1127_);
lean_inc(v_moreLinkObjs_1126_);
lean_inc(v_weakLeancArgs_1125_);
lean_inc(v_moreServerOptions_1124_);
lean_inc(v_moreLeancArgs_1123_);
lean_inc(v_weakLeanArgs_1122_);
lean_inc(v_moreLeanArgs_1121_);
lean_inc(v_leanOptions_1120_);
lean_dec(v_cfg_1118_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1146_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1140_ = lean_box(v_buildType_1119_);
v___x_1141_ = lean_apply_1(v_f_1117_, v___x_1140_);
if (v_isShared_1139_ == 0)
{
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_leanOptions_1120_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_moreLeanArgs_1121_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_weakLeanArgs_1122_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_moreLeancArgs_1123_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_moreServerOptions_1124_);
lean_ctor_set(v_reuseFailAlloc_1145_, 5, v_weakLeancArgs_1125_);
lean_ctor_set(v_reuseFailAlloc_1145_, 6, v_moreLinkObjs_1126_);
lean_ctor_set(v_reuseFailAlloc_1145_, 7, v_moreLinkLibs_1127_);
lean_ctor_set(v_reuseFailAlloc_1145_, 8, v_moreLinkArgs_1128_);
lean_ctor_set(v_reuseFailAlloc_1145_, 9, v_weakLinkArgs_1129_);
lean_ctor_set(v_reuseFailAlloc_1145_, 10, v_platformIndependent_1131_);
lean_ctor_set(v_reuseFailAlloc_1145_, 11, v_dynlibs_1133_);
lean_ctor_set(v_reuseFailAlloc_1145_, 12, v_plugins_1134_);
v___x_1143_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_unbox(v___x_1141_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*13, v___x_1144_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*13 + 1, v_backend_1130_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*13 + 2, v_precompileImports_1132_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1135_);
lean_ctor_set_uint8(v___x_1143_, sizeof(void*)*13 + 4, v_allowNonModules_1136_);
return v___x_1143_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1147_){
_start:
{
uint8_t v___x_1148_; 
v___x_1148_ = 3;
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1149_){
_start:
{
uint8_t v_res_1150_; lean_object* v_r_1151_; 
v_res_1150_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1149_);
lean_dec_ref(v_x_1149_);
v_r_1151_ = lean_box(v_res_1150_);
return v_r_1151_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1163_){
_start:
{
lean_object* v_leanOptions_1164_; 
v_leanOptions_1164_ = lean_ctor_get(v_cfg_1163_, 0);
lean_inc_ref(v_leanOptions_1164_);
return v_leanOptions_1164_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1165_);
lean_dec_ref(v_cfg_1165_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1167_, lean_object* v_cfg_1168_){
_start:
{
uint8_t v_buildType_1169_; lean_object* v_moreLeanArgs_1170_; lean_object* v_weakLeanArgs_1171_; lean_object* v_moreLeancArgs_1172_; lean_object* v_moreServerOptions_1173_; lean_object* v_weakLeancArgs_1174_; lean_object* v_moreLinkObjs_1175_; lean_object* v_moreLinkLibs_1176_; lean_object* v_moreLinkArgs_1177_; lean_object* v_weakLinkArgs_1178_; uint8_t v_backend_1179_; lean_object* v_platformIndependent_1180_; uint8_t v_precompileImports_1181_; lean_object* v_dynlibs_1182_; lean_object* v_plugins_1183_; uint8_t v_requiresModuleSystem_1184_; uint8_t v_allowNonModules_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1192_; 
v_buildType_1169_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*13);
v_moreLeanArgs_1170_ = lean_ctor_get(v_cfg_1168_, 1);
v_weakLeanArgs_1171_ = lean_ctor_get(v_cfg_1168_, 2);
v_moreLeancArgs_1172_ = lean_ctor_get(v_cfg_1168_, 3);
v_moreServerOptions_1173_ = lean_ctor_get(v_cfg_1168_, 4);
v_weakLeancArgs_1174_ = lean_ctor_get(v_cfg_1168_, 5);
v_moreLinkObjs_1175_ = lean_ctor_get(v_cfg_1168_, 6);
v_moreLinkLibs_1176_ = lean_ctor_get(v_cfg_1168_, 7);
v_moreLinkArgs_1177_ = lean_ctor_get(v_cfg_1168_, 8);
v_weakLinkArgs_1178_ = lean_ctor_get(v_cfg_1168_, 9);
v_backend_1179_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*13 + 1);
v_platformIndependent_1180_ = lean_ctor_get(v_cfg_1168_, 10);
v_precompileImports_1181_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*13 + 2);
v_dynlibs_1182_ = lean_ctor_get(v_cfg_1168_, 11);
v_plugins_1183_ = lean_ctor_get(v_cfg_1168_, 12);
v_requiresModuleSystem_1184_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*13 + 3);
v_allowNonModules_1185_ = lean_ctor_get_uint8(v_cfg_1168_, sizeof(void*)*13 + 4);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_cfg_1168_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_cfg_1168_, 0);
lean_dec(v_unused_1193_);
v___x_1187_ = v_cfg_1168_;
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_plugins_1183_);
lean_inc(v_dynlibs_1182_);
lean_inc(v_platformIndependent_1180_);
lean_inc(v_weakLinkArgs_1178_);
lean_inc(v_moreLinkArgs_1177_);
lean_inc(v_moreLinkLibs_1176_);
lean_inc(v_moreLinkObjs_1175_);
lean_inc(v_weakLeancArgs_1174_);
lean_inc(v_moreServerOptions_1173_);
lean_inc(v_moreLeancArgs_1172_);
lean_inc(v_weakLeanArgs_1171_);
lean_inc(v_moreLeanArgs_1170_);
lean_dec(v_cfg_1168_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1192_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v_val_1167_);
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_val_1167_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_moreLeanArgs_1170_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_weakLeanArgs_1171_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v_moreLeancArgs_1172_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v_moreServerOptions_1173_);
lean_ctor_set(v_reuseFailAlloc_1191_, 5, v_weakLeancArgs_1174_);
lean_ctor_set(v_reuseFailAlloc_1191_, 6, v_moreLinkObjs_1175_);
lean_ctor_set(v_reuseFailAlloc_1191_, 7, v_moreLinkLibs_1176_);
lean_ctor_set(v_reuseFailAlloc_1191_, 8, v_moreLinkArgs_1177_);
lean_ctor_set(v_reuseFailAlloc_1191_, 9, v_weakLinkArgs_1178_);
lean_ctor_set(v_reuseFailAlloc_1191_, 10, v_platformIndependent_1180_);
lean_ctor_set(v_reuseFailAlloc_1191_, 11, v_dynlibs_1182_);
lean_ctor_set(v_reuseFailAlloc_1191_, 12, v_plugins_1183_);
lean_ctor_set_uint8(v_reuseFailAlloc_1191_, sizeof(void*)*13, v_buildType_1169_);
lean_ctor_set_uint8(v_reuseFailAlloc_1191_, sizeof(void*)*13 + 1, v_backend_1179_);
lean_ctor_set_uint8(v_reuseFailAlloc_1191_, sizeof(void*)*13 + 2, v_precompileImports_1181_);
lean_ctor_set_uint8(v_reuseFailAlloc_1191_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1191_, sizeof(void*)*13 + 4, v_allowNonModules_1185_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1194_, lean_object* v_cfg_1195_){
_start:
{
uint8_t v_buildType_1196_; lean_object* v_leanOptions_1197_; lean_object* v_moreLeanArgs_1198_; lean_object* v_weakLeanArgs_1199_; lean_object* v_moreLeancArgs_1200_; lean_object* v_moreServerOptions_1201_; lean_object* v_weakLeancArgs_1202_; lean_object* v_moreLinkObjs_1203_; lean_object* v_moreLinkLibs_1204_; lean_object* v_moreLinkArgs_1205_; lean_object* v_weakLinkArgs_1206_; uint8_t v_backend_1207_; lean_object* v_platformIndependent_1208_; uint8_t v_precompileImports_1209_; lean_object* v_dynlibs_1210_; lean_object* v_plugins_1211_; uint8_t v_requiresModuleSystem_1212_; uint8_t v_allowNonModules_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_buildType_1196_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*13);
v_leanOptions_1197_ = lean_ctor_get(v_cfg_1195_, 0);
v_moreLeanArgs_1198_ = lean_ctor_get(v_cfg_1195_, 1);
v_weakLeanArgs_1199_ = lean_ctor_get(v_cfg_1195_, 2);
v_moreLeancArgs_1200_ = lean_ctor_get(v_cfg_1195_, 3);
v_moreServerOptions_1201_ = lean_ctor_get(v_cfg_1195_, 4);
v_weakLeancArgs_1202_ = lean_ctor_get(v_cfg_1195_, 5);
v_moreLinkObjs_1203_ = lean_ctor_get(v_cfg_1195_, 6);
v_moreLinkLibs_1204_ = lean_ctor_get(v_cfg_1195_, 7);
v_moreLinkArgs_1205_ = lean_ctor_get(v_cfg_1195_, 8);
v_weakLinkArgs_1206_ = lean_ctor_get(v_cfg_1195_, 9);
v_backend_1207_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*13 + 1);
v_platformIndependent_1208_ = lean_ctor_get(v_cfg_1195_, 10);
v_precompileImports_1209_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*13 + 2);
v_dynlibs_1210_ = lean_ctor_get(v_cfg_1195_, 11);
v_plugins_1211_ = lean_ctor_get(v_cfg_1195_, 12);
v_requiresModuleSystem_1212_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*13 + 3);
v_allowNonModules_1213_ = lean_ctor_get_uint8(v_cfg_1195_, sizeof(void*)*13 + 4);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_cfg_1195_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v_cfg_1195_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_plugins_1211_);
lean_inc(v_dynlibs_1210_);
lean_inc(v_platformIndependent_1208_);
lean_inc(v_weakLinkArgs_1206_);
lean_inc(v_moreLinkArgs_1205_);
lean_inc(v_moreLinkLibs_1204_);
lean_inc(v_moreLinkObjs_1203_);
lean_inc(v_weakLeancArgs_1202_);
lean_inc(v_moreServerOptions_1201_);
lean_inc(v_moreLeancArgs_1200_);
lean_inc(v_weakLeanArgs_1199_);
lean_inc(v_moreLeanArgs_1198_);
lean_inc(v_leanOptions_1197_);
lean_dec(v_cfg_1195_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_apply_1(v_f_1194_, v_leanOptions_1197_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_moreLeanArgs_1198_);
lean_ctor_set(v_reuseFailAlloc_1220_, 2, v_weakLeanArgs_1199_);
lean_ctor_set(v_reuseFailAlloc_1220_, 3, v_moreLeancArgs_1200_);
lean_ctor_set(v_reuseFailAlloc_1220_, 4, v_moreServerOptions_1201_);
lean_ctor_set(v_reuseFailAlloc_1220_, 5, v_weakLeancArgs_1202_);
lean_ctor_set(v_reuseFailAlloc_1220_, 6, v_moreLinkObjs_1203_);
lean_ctor_set(v_reuseFailAlloc_1220_, 7, v_moreLinkLibs_1204_);
lean_ctor_set(v_reuseFailAlloc_1220_, 8, v_moreLinkArgs_1205_);
lean_ctor_set(v_reuseFailAlloc_1220_, 9, v_weakLinkArgs_1206_);
lean_ctor_set(v_reuseFailAlloc_1220_, 10, v_platformIndependent_1208_);
lean_ctor_set(v_reuseFailAlloc_1220_, 11, v_dynlibs_1210_);
lean_ctor_set(v_reuseFailAlloc_1220_, 12, v_plugins_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*13, v_buildType_1196_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*13 + 1, v_backend_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*13 + 2, v_precompileImports_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1212_);
lean_ctor_set_uint8(v_reuseFailAlloc_1220_, sizeof(void*)*13 + 4, v_allowNonModules_1213_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1222_){
_start:
{
lean_object* v___x_1223_; 
v___x_1223_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1224_);
lean_dec_ref(v_x_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1237_){
_start:
{
lean_object* v_moreLeanArgs_1238_; 
v_moreLeanArgs_1238_ = lean_ctor_get(v_cfg_1237_, 1);
lean_inc_ref(v_moreLeanArgs_1238_);
return v_moreLeanArgs_1238_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1239_);
lean_dec_ref(v_cfg_1239_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1241_, lean_object* v_cfg_1242_){
_start:
{
uint8_t v_buildType_1243_; lean_object* v_leanOptions_1244_; lean_object* v_weakLeanArgs_1245_; lean_object* v_moreLeancArgs_1246_; lean_object* v_moreServerOptions_1247_; lean_object* v_weakLeancArgs_1248_; lean_object* v_moreLinkObjs_1249_; lean_object* v_moreLinkLibs_1250_; lean_object* v_moreLinkArgs_1251_; lean_object* v_weakLinkArgs_1252_; uint8_t v_backend_1253_; lean_object* v_platformIndependent_1254_; uint8_t v_precompileImports_1255_; lean_object* v_dynlibs_1256_; lean_object* v_plugins_1257_; uint8_t v_requiresModuleSystem_1258_; uint8_t v_allowNonModules_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_buildType_1243_ = lean_ctor_get_uint8(v_cfg_1242_, sizeof(void*)*13);
v_leanOptions_1244_ = lean_ctor_get(v_cfg_1242_, 0);
v_weakLeanArgs_1245_ = lean_ctor_get(v_cfg_1242_, 2);
v_moreLeancArgs_1246_ = lean_ctor_get(v_cfg_1242_, 3);
v_moreServerOptions_1247_ = lean_ctor_get(v_cfg_1242_, 4);
v_weakLeancArgs_1248_ = lean_ctor_get(v_cfg_1242_, 5);
v_moreLinkObjs_1249_ = lean_ctor_get(v_cfg_1242_, 6);
v_moreLinkLibs_1250_ = lean_ctor_get(v_cfg_1242_, 7);
v_moreLinkArgs_1251_ = lean_ctor_get(v_cfg_1242_, 8);
v_weakLinkArgs_1252_ = lean_ctor_get(v_cfg_1242_, 9);
v_backend_1253_ = lean_ctor_get_uint8(v_cfg_1242_, sizeof(void*)*13 + 1);
v_platformIndependent_1254_ = lean_ctor_get(v_cfg_1242_, 10);
v_precompileImports_1255_ = lean_ctor_get_uint8(v_cfg_1242_, sizeof(void*)*13 + 2);
v_dynlibs_1256_ = lean_ctor_get(v_cfg_1242_, 11);
v_plugins_1257_ = lean_ctor_get(v_cfg_1242_, 12);
v_requiresModuleSystem_1258_ = lean_ctor_get_uint8(v_cfg_1242_, sizeof(void*)*13 + 3);
v_allowNonModules_1259_ = lean_ctor_get_uint8(v_cfg_1242_, sizeof(void*)*13 + 4);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_cfg_1242_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v_cfg_1242_, 1);
lean_dec(v_unused_1267_);
v___x_1261_ = v_cfg_1242_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_plugins_1257_);
lean_inc(v_dynlibs_1256_);
lean_inc(v_platformIndependent_1254_);
lean_inc(v_weakLinkArgs_1252_);
lean_inc(v_moreLinkArgs_1251_);
lean_inc(v_moreLinkLibs_1250_);
lean_inc(v_moreLinkObjs_1249_);
lean_inc(v_weakLeancArgs_1248_);
lean_inc(v_moreServerOptions_1247_);
lean_inc(v_moreLeancArgs_1246_);
lean_inc(v_weakLeanArgs_1245_);
lean_inc(v_leanOptions_1244_);
lean_dec(v_cfg_1242_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_val_1241_);
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_leanOptions_1244_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_val_1241_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_weakLeanArgs_1245_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_moreLeancArgs_1246_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_moreServerOptions_1247_);
lean_ctor_set(v_reuseFailAlloc_1265_, 5, v_weakLeancArgs_1248_);
lean_ctor_set(v_reuseFailAlloc_1265_, 6, v_moreLinkObjs_1249_);
lean_ctor_set(v_reuseFailAlloc_1265_, 7, v_moreLinkLibs_1250_);
lean_ctor_set(v_reuseFailAlloc_1265_, 8, v_moreLinkArgs_1251_);
lean_ctor_set(v_reuseFailAlloc_1265_, 9, v_weakLinkArgs_1252_);
lean_ctor_set(v_reuseFailAlloc_1265_, 10, v_platformIndependent_1254_);
lean_ctor_set(v_reuseFailAlloc_1265_, 11, v_dynlibs_1256_);
lean_ctor_set(v_reuseFailAlloc_1265_, 12, v_plugins_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*13, v_buildType_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*13 + 1, v_backend_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*13 + 2, v_precompileImports_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*13 + 4, v_allowNonModules_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1268_, lean_object* v_cfg_1269_){
_start:
{
uint8_t v_buildType_1270_; lean_object* v_leanOptions_1271_; lean_object* v_moreLeanArgs_1272_; lean_object* v_weakLeanArgs_1273_; lean_object* v_moreLeancArgs_1274_; lean_object* v_moreServerOptions_1275_; lean_object* v_weakLeancArgs_1276_; lean_object* v_moreLinkObjs_1277_; lean_object* v_moreLinkLibs_1278_; lean_object* v_moreLinkArgs_1279_; lean_object* v_weakLinkArgs_1280_; uint8_t v_backend_1281_; lean_object* v_platformIndependent_1282_; uint8_t v_precompileImports_1283_; lean_object* v_dynlibs_1284_; lean_object* v_plugins_1285_; uint8_t v_requiresModuleSystem_1286_; uint8_t v_allowNonModules_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1295_; 
v_buildType_1270_ = lean_ctor_get_uint8(v_cfg_1269_, sizeof(void*)*13);
v_leanOptions_1271_ = lean_ctor_get(v_cfg_1269_, 0);
v_moreLeanArgs_1272_ = lean_ctor_get(v_cfg_1269_, 1);
v_weakLeanArgs_1273_ = lean_ctor_get(v_cfg_1269_, 2);
v_moreLeancArgs_1274_ = lean_ctor_get(v_cfg_1269_, 3);
v_moreServerOptions_1275_ = lean_ctor_get(v_cfg_1269_, 4);
v_weakLeancArgs_1276_ = lean_ctor_get(v_cfg_1269_, 5);
v_moreLinkObjs_1277_ = lean_ctor_get(v_cfg_1269_, 6);
v_moreLinkLibs_1278_ = lean_ctor_get(v_cfg_1269_, 7);
v_moreLinkArgs_1279_ = lean_ctor_get(v_cfg_1269_, 8);
v_weakLinkArgs_1280_ = lean_ctor_get(v_cfg_1269_, 9);
v_backend_1281_ = lean_ctor_get_uint8(v_cfg_1269_, sizeof(void*)*13 + 1);
v_platformIndependent_1282_ = lean_ctor_get(v_cfg_1269_, 10);
v_precompileImports_1283_ = lean_ctor_get_uint8(v_cfg_1269_, sizeof(void*)*13 + 2);
v_dynlibs_1284_ = lean_ctor_get(v_cfg_1269_, 11);
v_plugins_1285_ = lean_ctor_get(v_cfg_1269_, 12);
v_requiresModuleSystem_1286_ = lean_ctor_get_uint8(v_cfg_1269_, sizeof(void*)*13 + 3);
v_allowNonModules_1287_ = lean_ctor_get_uint8(v_cfg_1269_, sizeof(void*)*13 + 4);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_cfg_1269_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1289_ = v_cfg_1269_;
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_plugins_1285_);
lean_inc(v_dynlibs_1284_);
lean_inc(v_platformIndependent_1282_);
lean_inc(v_weakLinkArgs_1280_);
lean_inc(v_moreLinkArgs_1279_);
lean_inc(v_moreLinkLibs_1278_);
lean_inc(v_moreLinkObjs_1277_);
lean_inc(v_weakLeancArgs_1276_);
lean_inc(v_moreServerOptions_1275_);
lean_inc(v_moreLeancArgs_1274_);
lean_inc(v_weakLeanArgs_1273_);
lean_inc(v_moreLeanArgs_1272_);
lean_inc(v_leanOptions_1271_);
lean_dec(v_cfg_1269_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1295_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1291_ = lean_apply_1(v_f_1268_, v_moreLeanArgs_1272_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v___x_1291_);
v___x_1293_ = v___x_1289_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_leanOptions_1271_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_weakLeanArgs_1273_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_moreLeancArgs_1274_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_moreServerOptions_1275_);
lean_ctor_set(v_reuseFailAlloc_1294_, 5, v_weakLeancArgs_1276_);
lean_ctor_set(v_reuseFailAlloc_1294_, 6, v_moreLinkObjs_1277_);
lean_ctor_set(v_reuseFailAlloc_1294_, 7, v_moreLinkLibs_1278_);
lean_ctor_set(v_reuseFailAlloc_1294_, 8, v_moreLinkArgs_1279_);
lean_ctor_set(v_reuseFailAlloc_1294_, 9, v_weakLinkArgs_1280_);
lean_ctor_set(v_reuseFailAlloc_1294_, 10, v_platformIndependent_1282_);
lean_ctor_set(v_reuseFailAlloc_1294_, 11, v_dynlibs_1284_);
lean_ctor_set(v_reuseFailAlloc_1294_, 12, v_plugins_1285_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*13, v_buildType_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*13 + 1, v_backend_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*13 + 2, v_precompileImports_1283_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1286_);
lean_ctor_set_uint8(v_reuseFailAlloc_1294_, sizeof(void*)*13 + 4, v_allowNonModules_1287_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1296_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = ((lean_object*)(l_Lake_BuildType_leanArgs___redArg___closed__0));
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1298_);
lean_dec_ref(v_x_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1311_){
_start:
{
lean_object* v_weakLeanArgs_1312_; 
v_weakLeanArgs_1312_ = lean_ctor_get(v_cfg_1311_, 2);
lean_inc_ref(v_weakLeanArgs_1312_);
return v_weakLeanArgs_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1313_);
lean_dec_ref(v_cfg_1313_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1315_, lean_object* v_cfg_1316_){
_start:
{
uint8_t v_buildType_1317_; lean_object* v_leanOptions_1318_; lean_object* v_moreLeanArgs_1319_; lean_object* v_moreLeancArgs_1320_; lean_object* v_moreServerOptions_1321_; lean_object* v_weakLeancArgs_1322_; lean_object* v_moreLinkObjs_1323_; lean_object* v_moreLinkLibs_1324_; lean_object* v_moreLinkArgs_1325_; lean_object* v_weakLinkArgs_1326_; uint8_t v_backend_1327_; lean_object* v_platformIndependent_1328_; uint8_t v_precompileImports_1329_; lean_object* v_dynlibs_1330_; lean_object* v_plugins_1331_; uint8_t v_requiresModuleSystem_1332_; uint8_t v_allowNonModules_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_buildType_1317_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*13);
v_leanOptions_1318_ = lean_ctor_get(v_cfg_1316_, 0);
v_moreLeanArgs_1319_ = lean_ctor_get(v_cfg_1316_, 1);
v_moreLeancArgs_1320_ = lean_ctor_get(v_cfg_1316_, 3);
v_moreServerOptions_1321_ = lean_ctor_get(v_cfg_1316_, 4);
v_weakLeancArgs_1322_ = lean_ctor_get(v_cfg_1316_, 5);
v_moreLinkObjs_1323_ = lean_ctor_get(v_cfg_1316_, 6);
v_moreLinkLibs_1324_ = lean_ctor_get(v_cfg_1316_, 7);
v_moreLinkArgs_1325_ = lean_ctor_get(v_cfg_1316_, 8);
v_weakLinkArgs_1326_ = lean_ctor_get(v_cfg_1316_, 9);
v_backend_1327_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*13 + 1);
v_platformIndependent_1328_ = lean_ctor_get(v_cfg_1316_, 10);
v_precompileImports_1329_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*13 + 2);
v_dynlibs_1330_ = lean_ctor_get(v_cfg_1316_, 11);
v_plugins_1331_ = lean_ctor_get(v_cfg_1316_, 12);
v_requiresModuleSystem_1332_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*13 + 3);
v_allowNonModules_1333_ = lean_ctor_get_uint8(v_cfg_1316_, sizeof(void*)*13 + 4);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_cfg_1316_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_cfg_1316_, 2);
lean_dec(v_unused_1341_);
v___x_1335_ = v_cfg_1316_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_plugins_1331_);
lean_inc(v_dynlibs_1330_);
lean_inc(v_platformIndependent_1328_);
lean_inc(v_weakLinkArgs_1326_);
lean_inc(v_moreLinkArgs_1325_);
lean_inc(v_moreLinkLibs_1324_);
lean_inc(v_moreLinkObjs_1323_);
lean_inc(v_weakLeancArgs_1322_);
lean_inc(v_moreServerOptions_1321_);
lean_inc(v_moreLeancArgs_1320_);
lean_inc(v_moreLeanArgs_1319_);
lean_inc(v_leanOptions_1318_);
lean_dec(v_cfg_1316_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 2, v_val_1315_);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_leanOptions_1318_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_moreLeanArgs_1319_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_val_1315_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_moreLeancArgs_1320_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_moreServerOptions_1321_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v_weakLeancArgs_1322_);
lean_ctor_set(v_reuseFailAlloc_1339_, 6, v_moreLinkObjs_1323_);
lean_ctor_set(v_reuseFailAlloc_1339_, 7, v_moreLinkLibs_1324_);
lean_ctor_set(v_reuseFailAlloc_1339_, 8, v_moreLinkArgs_1325_);
lean_ctor_set(v_reuseFailAlloc_1339_, 9, v_weakLinkArgs_1326_);
lean_ctor_set(v_reuseFailAlloc_1339_, 10, v_platformIndependent_1328_);
lean_ctor_set(v_reuseFailAlloc_1339_, 11, v_dynlibs_1330_);
lean_ctor_set(v_reuseFailAlloc_1339_, 12, v_plugins_1331_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*13, v_buildType_1317_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*13 + 1, v_backend_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*13 + 2, v_precompileImports_1329_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1332_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*13 + 4, v_allowNonModules_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1342_, lean_object* v_cfg_1343_){
_start:
{
uint8_t v_buildType_1344_; lean_object* v_leanOptions_1345_; lean_object* v_moreLeanArgs_1346_; lean_object* v_weakLeanArgs_1347_; lean_object* v_moreLeancArgs_1348_; lean_object* v_moreServerOptions_1349_; lean_object* v_weakLeancArgs_1350_; lean_object* v_moreLinkObjs_1351_; lean_object* v_moreLinkLibs_1352_; lean_object* v_moreLinkArgs_1353_; lean_object* v_weakLinkArgs_1354_; uint8_t v_backend_1355_; lean_object* v_platformIndependent_1356_; uint8_t v_precompileImports_1357_; lean_object* v_dynlibs_1358_; lean_object* v_plugins_1359_; uint8_t v_requiresModuleSystem_1360_; uint8_t v_allowNonModules_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1369_; 
v_buildType_1344_ = lean_ctor_get_uint8(v_cfg_1343_, sizeof(void*)*13);
v_leanOptions_1345_ = lean_ctor_get(v_cfg_1343_, 0);
v_moreLeanArgs_1346_ = lean_ctor_get(v_cfg_1343_, 1);
v_weakLeanArgs_1347_ = lean_ctor_get(v_cfg_1343_, 2);
v_moreLeancArgs_1348_ = lean_ctor_get(v_cfg_1343_, 3);
v_moreServerOptions_1349_ = lean_ctor_get(v_cfg_1343_, 4);
v_weakLeancArgs_1350_ = lean_ctor_get(v_cfg_1343_, 5);
v_moreLinkObjs_1351_ = lean_ctor_get(v_cfg_1343_, 6);
v_moreLinkLibs_1352_ = lean_ctor_get(v_cfg_1343_, 7);
v_moreLinkArgs_1353_ = lean_ctor_get(v_cfg_1343_, 8);
v_weakLinkArgs_1354_ = lean_ctor_get(v_cfg_1343_, 9);
v_backend_1355_ = lean_ctor_get_uint8(v_cfg_1343_, sizeof(void*)*13 + 1);
v_platformIndependent_1356_ = lean_ctor_get(v_cfg_1343_, 10);
v_precompileImports_1357_ = lean_ctor_get_uint8(v_cfg_1343_, sizeof(void*)*13 + 2);
v_dynlibs_1358_ = lean_ctor_get(v_cfg_1343_, 11);
v_plugins_1359_ = lean_ctor_get(v_cfg_1343_, 12);
v_requiresModuleSystem_1360_ = lean_ctor_get_uint8(v_cfg_1343_, sizeof(void*)*13 + 3);
v_allowNonModules_1361_ = lean_ctor_get_uint8(v_cfg_1343_, sizeof(void*)*13 + 4);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_cfg_1343_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1363_ = v_cfg_1343_;
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_plugins_1359_);
lean_inc(v_dynlibs_1358_);
lean_inc(v_platformIndependent_1356_);
lean_inc(v_weakLinkArgs_1354_);
lean_inc(v_moreLinkArgs_1353_);
lean_inc(v_moreLinkLibs_1352_);
lean_inc(v_moreLinkObjs_1351_);
lean_inc(v_weakLeancArgs_1350_);
lean_inc(v_moreServerOptions_1349_);
lean_inc(v_moreLeancArgs_1348_);
lean_inc(v_weakLeanArgs_1347_);
lean_inc(v_moreLeanArgs_1346_);
lean_inc(v_leanOptions_1345_);
lean_dec(v_cfg_1343_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1369_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = lean_apply_1(v_f_1342_, v_weakLeanArgs_1347_);
if (v_isShared_1364_ == 0)
{
lean_ctor_set(v___x_1363_, 2, v___x_1365_);
v___x_1367_ = v___x_1363_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_leanOptions_1345_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_moreLeanArgs_1346_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v_moreLeancArgs_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v_moreServerOptions_1349_);
lean_ctor_set(v_reuseFailAlloc_1368_, 5, v_weakLeancArgs_1350_);
lean_ctor_set(v_reuseFailAlloc_1368_, 6, v_moreLinkObjs_1351_);
lean_ctor_set(v_reuseFailAlloc_1368_, 7, v_moreLinkLibs_1352_);
lean_ctor_set(v_reuseFailAlloc_1368_, 8, v_moreLinkArgs_1353_);
lean_ctor_set(v_reuseFailAlloc_1368_, 9, v_weakLinkArgs_1354_);
lean_ctor_set(v_reuseFailAlloc_1368_, 10, v_platformIndependent_1356_);
lean_ctor_set(v_reuseFailAlloc_1368_, 11, v_dynlibs_1358_);
lean_ctor_set(v_reuseFailAlloc_1368_, 12, v_plugins_1359_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13, v_buildType_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 1, v_backend_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 2, v_precompileImports_1357_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1360_);
lean_ctor_set_uint8(v_reuseFailAlloc_1368_, sizeof(void*)*13 + 4, v_allowNonModules_1361_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1380_){
_start:
{
lean_object* v_moreLeancArgs_1381_; 
v_moreLeancArgs_1381_ = lean_ctor_get(v_cfg_1380_, 3);
lean_inc_ref(v_moreLeancArgs_1381_);
return v_moreLeancArgs_1381_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1382_);
lean_dec_ref(v_cfg_1382_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1384_, lean_object* v_cfg_1385_){
_start:
{
uint8_t v_buildType_1386_; lean_object* v_leanOptions_1387_; lean_object* v_moreLeanArgs_1388_; lean_object* v_weakLeanArgs_1389_; lean_object* v_moreServerOptions_1390_; lean_object* v_weakLeancArgs_1391_; lean_object* v_moreLinkObjs_1392_; lean_object* v_moreLinkLibs_1393_; lean_object* v_moreLinkArgs_1394_; lean_object* v_weakLinkArgs_1395_; uint8_t v_backend_1396_; lean_object* v_platformIndependent_1397_; uint8_t v_precompileImports_1398_; lean_object* v_dynlibs_1399_; lean_object* v_plugins_1400_; uint8_t v_requiresModuleSystem_1401_; uint8_t v_allowNonModules_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_buildType_1386_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13);
v_leanOptions_1387_ = lean_ctor_get(v_cfg_1385_, 0);
v_moreLeanArgs_1388_ = lean_ctor_get(v_cfg_1385_, 1);
v_weakLeanArgs_1389_ = lean_ctor_get(v_cfg_1385_, 2);
v_moreServerOptions_1390_ = lean_ctor_get(v_cfg_1385_, 4);
v_weakLeancArgs_1391_ = lean_ctor_get(v_cfg_1385_, 5);
v_moreLinkObjs_1392_ = lean_ctor_get(v_cfg_1385_, 6);
v_moreLinkLibs_1393_ = lean_ctor_get(v_cfg_1385_, 7);
v_moreLinkArgs_1394_ = lean_ctor_get(v_cfg_1385_, 8);
v_weakLinkArgs_1395_ = lean_ctor_get(v_cfg_1385_, 9);
v_backend_1396_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13 + 1);
v_platformIndependent_1397_ = lean_ctor_get(v_cfg_1385_, 10);
v_precompileImports_1398_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13 + 2);
v_dynlibs_1399_ = lean_ctor_get(v_cfg_1385_, 11);
v_plugins_1400_ = lean_ctor_get(v_cfg_1385_, 12);
v_requiresModuleSystem_1401_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13 + 3);
v_allowNonModules_1402_ = lean_ctor_get_uint8(v_cfg_1385_, sizeof(void*)*13 + 4);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_cfg_1385_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_cfg_1385_, 3);
lean_dec(v_unused_1410_);
v___x_1404_ = v_cfg_1385_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_plugins_1400_);
lean_inc(v_dynlibs_1399_);
lean_inc(v_platformIndependent_1397_);
lean_inc(v_weakLinkArgs_1395_);
lean_inc(v_moreLinkArgs_1394_);
lean_inc(v_moreLinkLibs_1393_);
lean_inc(v_moreLinkObjs_1392_);
lean_inc(v_weakLeancArgs_1391_);
lean_inc(v_moreServerOptions_1390_);
lean_inc(v_weakLeanArgs_1389_);
lean_inc(v_moreLeanArgs_1388_);
lean_inc(v_leanOptions_1387_);
lean_dec(v_cfg_1385_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 3, v_val_1384_);
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_leanOptions_1387_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_moreLeanArgs_1388_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_weakLeanArgs_1389_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_val_1384_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_moreServerOptions_1390_);
lean_ctor_set(v_reuseFailAlloc_1408_, 5, v_weakLeancArgs_1391_);
lean_ctor_set(v_reuseFailAlloc_1408_, 6, v_moreLinkObjs_1392_);
lean_ctor_set(v_reuseFailAlloc_1408_, 7, v_moreLinkLibs_1393_);
lean_ctor_set(v_reuseFailAlloc_1408_, 8, v_moreLinkArgs_1394_);
lean_ctor_set(v_reuseFailAlloc_1408_, 9, v_weakLinkArgs_1395_);
lean_ctor_set(v_reuseFailAlloc_1408_, 10, v_platformIndependent_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 11, v_dynlibs_1399_);
lean_ctor_set(v_reuseFailAlloc_1408_, 12, v_plugins_1400_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13, v_buildType_1386_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13 + 1, v_backend_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13 + 2, v_precompileImports_1398_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1401_);
lean_ctor_set_uint8(v_reuseFailAlloc_1408_, sizeof(void*)*13 + 4, v_allowNonModules_1402_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1411_, lean_object* v_cfg_1412_){
_start:
{
uint8_t v_buildType_1413_; lean_object* v_leanOptions_1414_; lean_object* v_moreLeanArgs_1415_; lean_object* v_weakLeanArgs_1416_; lean_object* v_moreLeancArgs_1417_; lean_object* v_moreServerOptions_1418_; lean_object* v_weakLeancArgs_1419_; lean_object* v_moreLinkObjs_1420_; lean_object* v_moreLinkLibs_1421_; lean_object* v_moreLinkArgs_1422_; lean_object* v_weakLinkArgs_1423_; uint8_t v_backend_1424_; lean_object* v_platformIndependent_1425_; uint8_t v_precompileImports_1426_; lean_object* v_dynlibs_1427_; lean_object* v_plugins_1428_; uint8_t v_requiresModuleSystem_1429_; uint8_t v_allowNonModules_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1438_; 
v_buildType_1413_ = lean_ctor_get_uint8(v_cfg_1412_, sizeof(void*)*13);
v_leanOptions_1414_ = lean_ctor_get(v_cfg_1412_, 0);
v_moreLeanArgs_1415_ = lean_ctor_get(v_cfg_1412_, 1);
v_weakLeanArgs_1416_ = lean_ctor_get(v_cfg_1412_, 2);
v_moreLeancArgs_1417_ = lean_ctor_get(v_cfg_1412_, 3);
v_moreServerOptions_1418_ = lean_ctor_get(v_cfg_1412_, 4);
v_weakLeancArgs_1419_ = lean_ctor_get(v_cfg_1412_, 5);
v_moreLinkObjs_1420_ = lean_ctor_get(v_cfg_1412_, 6);
v_moreLinkLibs_1421_ = lean_ctor_get(v_cfg_1412_, 7);
v_moreLinkArgs_1422_ = lean_ctor_get(v_cfg_1412_, 8);
v_weakLinkArgs_1423_ = lean_ctor_get(v_cfg_1412_, 9);
v_backend_1424_ = lean_ctor_get_uint8(v_cfg_1412_, sizeof(void*)*13 + 1);
v_platformIndependent_1425_ = lean_ctor_get(v_cfg_1412_, 10);
v_precompileImports_1426_ = lean_ctor_get_uint8(v_cfg_1412_, sizeof(void*)*13 + 2);
v_dynlibs_1427_ = lean_ctor_get(v_cfg_1412_, 11);
v_plugins_1428_ = lean_ctor_get(v_cfg_1412_, 12);
v_requiresModuleSystem_1429_ = lean_ctor_get_uint8(v_cfg_1412_, sizeof(void*)*13 + 3);
v_allowNonModules_1430_ = lean_ctor_get_uint8(v_cfg_1412_, sizeof(void*)*13 + 4);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_cfg_1412_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1432_ = v_cfg_1412_;
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_plugins_1428_);
lean_inc(v_dynlibs_1427_);
lean_inc(v_platformIndependent_1425_);
lean_inc(v_weakLinkArgs_1423_);
lean_inc(v_moreLinkArgs_1422_);
lean_inc(v_moreLinkLibs_1421_);
lean_inc(v_moreLinkObjs_1420_);
lean_inc(v_weakLeancArgs_1419_);
lean_inc(v_moreServerOptions_1418_);
lean_inc(v_moreLeancArgs_1417_);
lean_inc(v_weakLeanArgs_1416_);
lean_inc(v_moreLeanArgs_1415_);
lean_inc(v_leanOptions_1414_);
lean_dec(v_cfg_1412_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1438_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1434_ = lean_apply_1(v_f_1411_, v_moreLeancArgs_1417_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 3, v___x_1434_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_leanOptions_1414_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_moreLeanArgs_1415_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_weakLeanArgs_1416_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_moreServerOptions_1418_);
lean_ctor_set(v_reuseFailAlloc_1437_, 5, v_weakLeancArgs_1419_);
lean_ctor_set(v_reuseFailAlloc_1437_, 6, v_moreLinkObjs_1420_);
lean_ctor_set(v_reuseFailAlloc_1437_, 7, v_moreLinkLibs_1421_);
lean_ctor_set(v_reuseFailAlloc_1437_, 8, v_moreLinkArgs_1422_);
lean_ctor_set(v_reuseFailAlloc_1437_, 9, v_weakLinkArgs_1423_);
lean_ctor_set(v_reuseFailAlloc_1437_, 10, v_platformIndependent_1425_);
lean_ctor_set(v_reuseFailAlloc_1437_, 11, v_dynlibs_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 12, v_plugins_1428_);
lean_ctor_set_uint8(v_reuseFailAlloc_1437_, sizeof(void*)*13, v_buildType_1413_);
lean_ctor_set_uint8(v_reuseFailAlloc_1437_, sizeof(void*)*13 + 1, v_backend_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1437_, sizeof(void*)*13 + 2, v_precompileImports_1426_);
lean_ctor_set_uint8(v_reuseFailAlloc_1437_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1429_);
lean_ctor_set_uint8(v_reuseFailAlloc_1437_, sizeof(void*)*13 + 4, v_allowNonModules_1430_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1449_){
_start:
{
lean_object* v_moreServerOptions_1450_; 
v_moreServerOptions_1450_ = lean_ctor_get(v_cfg_1449_, 4);
lean_inc_ref(v_moreServerOptions_1450_);
return v_moreServerOptions_1450_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1451_);
lean_dec_ref(v_cfg_1451_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1453_, lean_object* v_cfg_1454_){
_start:
{
uint8_t v_buildType_1455_; lean_object* v_leanOptions_1456_; lean_object* v_moreLeanArgs_1457_; lean_object* v_weakLeanArgs_1458_; lean_object* v_moreLeancArgs_1459_; lean_object* v_weakLeancArgs_1460_; lean_object* v_moreLinkObjs_1461_; lean_object* v_moreLinkLibs_1462_; lean_object* v_moreLinkArgs_1463_; lean_object* v_weakLinkArgs_1464_; uint8_t v_backend_1465_; lean_object* v_platformIndependent_1466_; uint8_t v_precompileImports_1467_; lean_object* v_dynlibs_1468_; lean_object* v_plugins_1469_; uint8_t v_requiresModuleSystem_1470_; uint8_t v_allowNonModules_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
v_buildType_1455_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*13);
v_leanOptions_1456_ = lean_ctor_get(v_cfg_1454_, 0);
v_moreLeanArgs_1457_ = lean_ctor_get(v_cfg_1454_, 1);
v_weakLeanArgs_1458_ = lean_ctor_get(v_cfg_1454_, 2);
v_moreLeancArgs_1459_ = lean_ctor_get(v_cfg_1454_, 3);
v_weakLeancArgs_1460_ = lean_ctor_get(v_cfg_1454_, 5);
v_moreLinkObjs_1461_ = lean_ctor_get(v_cfg_1454_, 6);
v_moreLinkLibs_1462_ = lean_ctor_get(v_cfg_1454_, 7);
v_moreLinkArgs_1463_ = lean_ctor_get(v_cfg_1454_, 8);
v_weakLinkArgs_1464_ = lean_ctor_get(v_cfg_1454_, 9);
v_backend_1465_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*13 + 1);
v_platformIndependent_1466_ = lean_ctor_get(v_cfg_1454_, 10);
v_precompileImports_1467_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*13 + 2);
v_dynlibs_1468_ = lean_ctor_get(v_cfg_1454_, 11);
v_plugins_1469_ = lean_ctor_get(v_cfg_1454_, 12);
v_requiresModuleSystem_1470_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*13 + 3);
v_allowNonModules_1471_ = lean_ctor_get_uint8(v_cfg_1454_, sizeof(void*)*13 + 4);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_cfg_1454_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_cfg_1454_, 4);
lean_dec(v_unused_1479_);
v___x_1473_ = v_cfg_1454_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_plugins_1469_);
lean_inc(v_dynlibs_1468_);
lean_inc(v_platformIndependent_1466_);
lean_inc(v_weakLinkArgs_1464_);
lean_inc(v_moreLinkArgs_1463_);
lean_inc(v_moreLinkLibs_1462_);
lean_inc(v_moreLinkObjs_1461_);
lean_inc(v_weakLeancArgs_1460_);
lean_inc(v_moreLeancArgs_1459_);
lean_inc(v_weakLeanArgs_1458_);
lean_inc(v_moreLeanArgs_1457_);
lean_inc(v_leanOptions_1456_);
lean_dec(v_cfg_1454_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v_val_1453_);
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_leanOptions_1456_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_moreLeanArgs_1457_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_weakLeanArgs_1458_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_moreLeancArgs_1459_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v_val_1453_);
lean_ctor_set(v_reuseFailAlloc_1477_, 5, v_weakLeancArgs_1460_);
lean_ctor_set(v_reuseFailAlloc_1477_, 6, v_moreLinkObjs_1461_);
lean_ctor_set(v_reuseFailAlloc_1477_, 7, v_moreLinkLibs_1462_);
lean_ctor_set(v_reuseFailAlloc_1477_, 8, v_moreLinkArgs_1463_);
lean_ctor_set(v_reuseFailAlloc_1477_, 9, v_weakLinkArgs_1464_);
lean_ctor_set(v_reuseFailAlloc_1477_, 10, v_platformIndependent_1466_);
lean_ctor_set(v_reuseFailAlloc_1477_, 11, v_dynlibs_1468_);
lean_ctor_set(v_reuseFailAlloc_1477_, 12, v_plugins_1469_);
lean_ctor_set_uint8(v_reuseFailAlloc_1477_, sizeof(void*)*13, v_buildType_1455_);
lean_ctor_set_uint8(v_reuseFailAlloc_1477_, sizeof(void*)*13 + 1, v_backend_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1477_, sizeof(void*)*13 + 2, v_precompileImports_1467_);
lean_ctor_set_uint8(v_reuseFailAlloc_1477_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1477_, sizeof(void*)*13 + 4, v_allowNonModules_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1480_, lean_object* v_cfg_1481_){
_start:
{
uint8_t v_buildType_1482_; lean_object* v_leanOptions_1483_; lean_object* v_moreLeanArgs_1484_; lean_object* v_weakLeanArgs_1485_; lean_object* v_moreLeancArgs_1486_; lean_object* v_moreServerOptions_1487_; lean_object* v_weakLeancArgs_1488_; lean_object* v_moreLinkObjs_1489_; lean_object* v_moreLinkLibs_1490_; lean_object* v_moreLinkArgs_1491_; lean_object* v_weakLinkArgs_1492_; uint8_t v_backend_1493_; lean_object* v_platformIndependent_1494_; uint8_t v_precompileImports_1495_; lean_object* v_dynlibs_1496_; lean_object* v_plugins_1497_; uint8_t v_requiresModuleSystem_1498_; uint8_t v_allowNonModules_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1507_; 
v_buildType_1482_ = lean_ctor_get_uint8(v_cfg_1481_, sizeof(void*)*13);
v_leanOptions_1483_ = lean_ctor_get(v_cfg_1481_, 0);
v_moreLeanArgs_1484_ = lean_ctor_get(v_cfg_1481_, 1);
v_weakLeanArgs_1485_ = lean_ctor_get(v_cfg_1481_, 2);
v_moreLeancArgs_1486_ = lean_ctor_get(v_cfg_1481_, 3);
v_moreServerOptions_1487_ = lean_ctor_get(v_cfg_1481_, 4);
v_weakLeancArgs_1488_ = lean_ctor_get(v_cfg_1481_, 5);
v_moreLinkObjs_1489_ = lean_ctor_get(v_cfg_1481_, 6);
v_moreLinkLibs_1490_ = lean_ctor_get(v_cfg_1481_, 7);
v_moreLinkArgs_1491_ = lean_ctor_get(v_cfg_1481_, 8);
v_weakLinkArgs_1492_ = lean_ctor_get(v_cfg_1481_, 9);
v_backend_1493_ = lean_ctor_get_uint8(v_cfg_1481_, sizeof(void*)*13 + 1);
v_platformIndependent_1494_ = lean_ctor_get(v_cfg_1481_, 10);
v_precompileImports_1495_ = lean_ctor_get_uint8(v_cfg_1481_, sizeof(void*)*13 + 2);
v_dynlibs_1496_ = lean_ctor_get(v_cfg_1481_, 11);
v_plugins_1497_ = lean_ctor_get(v_cfg_1481_, 12);
v_requiresModuleSystem_1498_ = lean_ctor_get_uint8(v_cfg_1481_, sizeof(void*)*13 + 3);
v_allowNonModules_1499_ = lean_ctor_get_uint8(v_cfg_1481_, sizeof(void*)*13 + 4);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_cfg_1481_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1501_ = v_cfg_1481_;
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_plugins_1497_);
lean_inc(v_dynlibs_1496_);
lean_inc(v_platformIndependent_1494_);
lean_inc(v_weakLinkArgs_1492_);
lean_inc(v_moreLinkArgs_1491_);
lean_inc(v_moreLinkLibs_1490_);
lean_inc(v_moreLinkObjs_1489_);
lean_inc(v_weakLeancArgs_1488_);
lean_inc(v_moreServerOptions_1487_);
lean_inc(v_moreLeancArgs_1486_);
lean_inc(v_weakLeanArgs_1485_);
lean_inc(v_moreLeanArgs_1484_);
lean_inc(v_leanOptions_1483_);
lean_dec(v_cfg_1481_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_apply_1(v_f_1480_, v_moreServerOptions_1487_);
if (v_isShared_1502_ == 0)
{
lean_ctor_set(v___x_1501_, 4, v___x_1503_);
v___x_1505_ = v___x_1501_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_leanOptions_1483_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_moreLeanArgs_1484_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_weakLeanArgs_1485_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_moreLeancArgs_1486_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1506_, 5, v_weakLeancArgs_1488_);
lean_ctor_set(v_reuseFailAlloc_1506_, 6, v_moreLinkObjs_1489_);
lean_ctor_set(v_reuseFailAlloc_1506_, 7, v_moreLinkLibs_1490_);
lean_ctor_set(v_reuseFailAlloc_1506_, 8, v_moreLinkArgs_1491_);
lean_ctor_set(v_reuseFailAlloc_1506_, 9, v_weakLinkArgs_1492_);
lean_ctor_set(v_reuseFailAlloc_1506_, 10, v_platformIndependent_1494_);
lean_ctor_set(v_reuseFailAlloc_1506_, 11, v_dynlibs_1496_);
lean_ctor_set(v_reuseFailAlloc_1506_, 12, v_plugins_1497_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*13, v_buildType_1482_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*13 + 1, v_backend_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*13 + 2, v_precompileImports_1495_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1498_);
lean_ctor_set_uint8(v_reuseFailAlloc_1506_, sizeof(void*)*13 + 4, v_allowNonModules_1499_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1518_){
_start:
{
lean_object* v_weakLeancArgs_1519_; 
v_weakLeancArgs_1519_ = lean_ctor_get(v_cfg_1518_, 5);
lean_inc_ref(v_weakLeancArgs_1519_);
return v_weakLeancArgs_1519_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1520_);
lean_dec_ref(v_cfg_1520_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1522_, lean_object* v_cfg_1523_){
_start:
{
uint8_t v_buildType_1524_; lean_object* v_leanOptions_1525_; lean_object* v_moreLeanArgs_1526_; lean_object* v_weakLeanArgs_1527_; lean_object* v_moreLeancArgs_1528_; lean_object* v_moreServerOptions_1529_; lean_object* v_moreLinkObjs_1530_; lean_object* v_moreLinkLibs_1531_; lean_object* v_moreLinkArgs_1532_; lean_object* v_weakLinkArgs_1533_; uint8_t v_backend_1534_; lean_object* v_platformIndependent_1535_; uint8_t v_precompileImports_1536_; lean_object* v_dynlibs_1537_; lean_object* v_plugins_1538_; uint8_t v_requiresModuleSystem_1539_; uint8_t v_allowNonModules_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_buildType_1524_ = lean_ctor_get_uint8(v_cfg_1523_, sizeof(void*)*13);
v_leanOptions_1525_ = lean_ctor_get(v_cfg_1523_, 0);
v_moreLeanArgs_1526_ = lean_ctor_get(v_cfg_1523_, 1);
v_weakLeanArgs_1527_ = lean_ctor_get(v_cfg_1523_, 2);
v_moreLeancArgs_1528_ = lean_ctor_get(v_cfg_1523_, 3);
v_moreServerOptions_1529_ = lean_ctor_get(v_cfg_1523_, 4);
v_moreLinkObjs_1530_ = lean_ctor_get(v_cfg_1523_, 6);
v_moreLinkLibs_1531_ = lean_ctor_get(v_cfg_1523_, 7);
v_moreLinkArgs_1532_ = lean_ctor_get(v_cfg_1523_, 8);
v_weakLinkArgs_1533_ = lean_ctor_get(v_cfg_1523_, 9);
v_backend_1534_ = lean_ctor_get_uint8(v_cfg_1523_, sizeof(void*)*13 + 1);
v_platformIndependent_1535_ = lean_ctor_get(v_cfg_1523_, 10);
v_precompileImports_1536_ = lean_ctor_get_uint8(v_cfg_1523_, sizeof(void*)*13 + 2);
v_dynlibs_1537_ = lean_ctor_get(v_cfg_1523_, 11);
v_plugins_1538_ = lean_ctor_get(v_cfg_1523_, 12);
v_requiresModuleSystem_1539_ = lean_ctor_get_uint8(v_cfg_1523_, sizeof(void*)*13 + 3);
v_allowNonModules_1540_ = lean_ctor_get_uint8(v_cfg_1523_, sizeof(void*)*13 + 4);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_cfg_1523_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_cfg_1523_, 5);
lean_dec(v_unused_1548_);
v___x_1542_ = v_cfg_1523_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_plugins_1538_);
lean_inc(v_dynlibs_1537_);
lean_inc(v_platformIndependent_1535_);
lean_inc(v_weakLinkArgs_1533_);
lean_inc(v_moreLinkArgs_1532_);
lean_inc(v_moreLinkLibs_1531_);
lean_inc(v_moreLinkObjs_1530_);
lean_inc(v_moreServerOptions_1529_);
lean_inc(v_moreLeancArgs_1528_);
lean_inc(v_weakLeanArgs_1527_);
lean_inc(v_moreLeanArgs_1526_);
lean_inc(v_leanOptions_1525_);
lean_dec(v_cfg_1523_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 5, v_val_1522_);
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_leanOptions_1525_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_moreLeanArgs_1526_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_weakLeanArgs_1527_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_moreLeancArgs_1528_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_moreServerOptions_1529_);
lean_ctor_set(v_reuseFailAlloc_1546_, 5, v_val_1522_);
lean_ctor_set(v_reuseFailAlloc_1546_, 6, v_moreLinkObjs_1530_);
lean_ctor_set(v_reuseFailAlloc_1546_, 7, v_moreLinkLibs_1531_);
lean_ctor_set(v_reuseFailAlloc_1546_, 8, v_moreLinkArgs_1532_);
lean_ctor_set(v_reuseFailAlloc_1546_, 9, v_weakLinkArgs_1533_);
lean_ctor_set(v_reuseFailAlloc_1546_, 10, v_platformIndependent_1535_);
lean_ctor_set(v_reuseFailAlloc_1546_, 11, v_dynlibs_1537_);
lean_ctor_set(v_reuseFailAlloc_1546_, 12, v_plugins_1538_);
lean_ctor_set_uint8(v_reuseFailAlloc_1546_, sizeof(void*)*13, v_buildType_1524_);
lean_ctor_set_uint8(v_reuseFailAlloc_1546_, sizeof(void*)*13 + 1, v_backend_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1546_, sizeof(void*)*13 + 2, v_precompileImports_1536_);
lean_ctor_set_uint8(v_reuseFailAlloc_1546_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1539_);
lean_ctor_set_uint8(v_reuseFailAlloc_1546_, sizeof(void*)*13 + 4, v_allowNonModules_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1549_, lean_object* v_cfg_1550_){
_start:
{
uint8_t v_buildType_1551_; lean_object* v_leanOptions_1552_; lean_object* v_moreLeanArgs_1553_; lean_object* v_weakLeanArgs_1554_; lean_object* v_moreLeancArgs_1555_; lean_object* v_moreServerOptions_1556_; lean_object* v_weakLeancArgs_1557_; lean_object* v_moreLinkObjs_1558_; lean_object* v_moreLinkLibs_1559_; lean_object* v_moreLinkArgs_1560_; lean_object* v_weakLinkArgs_1561_; uint8_t v_backend_1562_; lean_object* v_platformIndependent_1563_; uint8_t v_precompileImports_1564_; lean_object* v_dynlibs_1565_; lean_object* v_plugins_1566_; uint8_t v_requiresModuleSystem_1567_; uint8_t v_allowNonModules_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1576_; 
v_buildType_1551_ = lean_ctor_get_uint8(v_cfg_1550_, sizeof(void*)*13);
v_leanOptions_1552_ = lean_ctor_get(v_cfg_1550_, 0);
v_moreLeanArgs_1553_ = lean_ctor_get(v_cfg_1550_, 1);
v_weakLeanArgs_1554_ = lean_ctor_get(v_cfg_1550_, 2);
v_moreLeancArgs_1555_ = lean_ctor_get(v_cfg_1550_, 3);
v_moreServerOptions_1556_ = lean_ctor_get(v_cfg_1550_, 4);
v_weakLeancArgs_1557_ = lean_ctor_get(v_cfg_1550_, 5);
v_moreLinkObjs_1558_ = lean_ctor_get(v_cfg_1550_, 6);
v_moreLinkLibs_1559_ = lean_ctor_get(v_cfg_1550_, 7);
v_moreLinkArgs_1560_ = lean_ctor_get(v_cfg_1550_, 8);
v_weakLinkArgs_1561_ = lean_ctor_get(v_cfg_1550_, 9);
v_backend_1562_ = lean_ctor_get_uint8(v_cfg_1550_, sizeof(void*)*13 + 1);
v_platformIndependent_1563_ = lean_ctor_get(v_cfg_1550_, 10);
v_precompileImports_1564_ = lean_ctor_get_uint8(v_cfg_1550_, sizeof(void*)*13 + 2);
v_dynlibs_1565_ = lean_ctor_get(v_cfg_1550_, 11);
v_plugins_1566_ = lean_ctor_get(v_cfg_1550_, 12);
v_requiresModuleSystem_1567_ = lean_ctor_get_uint8(v_cfg_1550_, sizeof(void*)*13 + 3);
v_allowNonModules_1568_ = lean_ctor_get_uint8(v_cfg_1550_, sizeof(void*)*13 + 4);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_cfg_1550_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1570_ = v_cfg_1550_;
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_plugins_1566_);
lean_inc(v_dynlibs_1565_);
lean_inc(v_platformIndependent_1563_);
lean_inc(v_weakLinkArgs_1561_);
lean_inc(v_moreLinkArgs_1560_);
lean_inc(v_moreLinkLibs_1559_);
lean_inc(v_moreLinkObjs_1558_);
lean_inc(v_weakLeancArgs_1557_);
lean_inc(v_moreServerOptions_1556_);
lean_inc(v_moreLeancArgs_1555_);
lean_inc(v_weakLeanArgs_1554_);
lean_inc(v_moreLeanArgs_1553_);
lean_inc(v_leanOptions_1552_);
lean_dec(v_cfg_1550_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = lean_apply_1(v_f_1549_, v_weakLeancArgs_1557_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 5, v___x_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_leanOptions_1552_);
lean_ctor_set(v_reuseFailAlloc_1575_, 1, v_moreLeanArgs_1553_);
lean_ctor_set(v_reuseFailAlloc_1575_, 2, v_weakLeanArgs_1554_);
lean_ctor_set(v_reuseFailAlloc_1575_, 3, v_moreLeancArgs_1555_);
lean_ctor_set(v_reuseFailAlloc_1575_, 4, v_moreServerOptions_1556_);
lean_ctor_set(v_reuseFailAlloc_1575_, 5, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1575_, 6, v_moreLinkObjs_1558_);
lean_ctor_set(v_reuseFailAlloc_1575_, 7, v_moreLinkLibs_1559_);
lean_ctor_set(v_reuseFailAlloc_1575_, 8, v_moreLinkArgs_1560_);
lean_ctor_set(v_reuseFailAlloc_1575_, 9, v_weakLinkArgs_1561_);
lean_ctor_set(v_reuseFailAlloc_1575_, 10, v_platformIndependent_1563_);
lean_ctor_set(v_reuseFailAlloc_1575_, 11, v_dynlibs_1565_);
lean_ctor_set(v_reuseFailAlloc_1575_, 12, v_plugins_1566_);
lean_ctor_set_uint8(v_reuseFailAlloc_1575_, sizeof(void*)*13, v_buildType_1551_);
lean_ctor_set_uint8(v_reuseFailAlloc_1575_, sizeof(void*)*13 + 1, v_backend_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1575_, sizeof(void*)*13 + 2, v_precompileImports_1564_);
lean_ctor_set_uint8(v_reuseFailAlloc_1575_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1567_);
lean_ctor_set_uint8(v_reuseFailAlloc_1575_, sizeof(void*)*13 + 4, v_allowNonModules_1568_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1587_){
_start:
{
lean_object* v_moreLinkObjs_1588_; 
v_moreLinkObjs_1588_ = lean_ctor_get(v_cfg_1587_, 6);
lean_inc_ref(v_moreLinkObjs_1588_);
return v_moreLinkObjs_1588_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1589_);
lean_dec_ref(v_cfg_1589_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1591_, lean_object* v_cfg_1592_){
_start:
{
uint8_t v_buildType_1593_; lean_object* v_leanOptions_1594_; lean_object* v_moreLeanArgs_1595_; lean_object* v_weakLeanArgs_1596_; lean_object* v_moreLeancArgs_1597_; lean_object* v_moreServerOptions_1598_; lean_object* v_weakLeancArgs_1599_; lean_object* v_moreLinkLibs_1600_; lean_object* v_moreLinkArgs_1601_; lean_object* v_weakLinkArgs_1602_; uint8_t v_backend_1603_; lean_object* v_platformIndependent_1604_; uint8_t v_precompileImports_1605_; lean_object* v_dynlibs_1606_; lean_object* v_plugins_1607_; uint8_t v_requiresModuleSystem_1608_; uint8_t v_allowNonModules_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_buildType_1593_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*13);
v_leanOptions_1594_ = lean_ctor_get(v_cfg_1592_, 0);
v_moreLeanArgs_1595_ = lean_ctor_get(v_cfg_1592_, 1);
v_weakLeanArgs_1596_ = lean_ctor_get(v_cfg_1592_, 2);
v_moreLeancArgs_1597_ = lean_ctor_get(v_cfg_1592_, 3);
v_moreServerOptions_1598_ = lean_ctor_get(v_cfg_1592_, 4);
v_weakLeancArgs_1599_ = lean_ctor_get(v_cfg_1592_, 5);
v_moreLinkLibs_1600_ = lean_ctor_get(v_cfg_1592_, 7);
v_moreLinkArgs_1601_ = lean_ctor_get(v_cfg_1592_, 8);
v_weakLinkArgs_1602_ = lean_ctor_get(v_cfg_1592_, 9);
v_backend_1603_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*13 + 1);
v_platformIndependent_1604_ = lean_ctor_get(v_cfg_1592_, 10);
v_precompileImports_1605_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*13 + 2);
v_dynlibs_1606_ = lean_ctor_get(v_cfg_1592_, 11);
v_plugins_1607_ = lean_ctor_get(v_cfg_1592_, 12);
v_requiresModuleSystem_1608_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*13 + 3);
v_allowNonModules_1609_ = lean_ctor_get_uint8(v_cfg_1592_, sizeof(void*)*13 + 4);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_cfg_1592_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; 
v_unused_1617_ = lean_ctor_get(v_cfg_1592_, 6);
lean_dec(v_unused_1617_);
v___x_1611_ = v_cfg_1592_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_plugins_1607_);
lean_inc(v_dynlibs_1606_);
lean_inc(v_platformIndependent_1604_);
lean_inc(v_weakLinkArgs_1602_);
lean_inc(v_moreLinkArgs_1601_);
lean_inc(v_moreLinkLibs_1600_);
lean_inc(v_weakLeancArgs_1599_);
lean_inc(v_moreServerOptions_1598_);
lean_inc(v_moreLeancArgs_1597_);
lean_inc(v_weakLeanArgs_1596_);
lean_inc(v_moreLeanArgs_1595_);
lean_inc(v_leanOptions_1594_);
lean_dec(v_cfg_1592_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 6, v_val_1591_);
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_leanOptions_1594_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_moreLeanArgs_1595_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_weakLeanArgs_1596_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_moreLeancArgs_1597_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_moreServerOptions_1598_);
lean_ctor_set(v_reuseFailAlloc_1615_, 5, v_weakLeancArgs_1599_);
lean_ctor_set(v_reuseFailAlloc_1615_, 6, v_val_1591_);
lean_ctor_set(v_reuseFailAlloc_1615_, 7, v_moreLinkLibs_1600_);
lean_ctor_set(v_reuseFailAlloc_1615_, 8, v_moreLinkArgs_1601_);
lean_ctor_set(v_reuseFailAlloc_1615_, 9, v_weakLinkArgs_1602_);
lean_ctor_set(v_reuseFailAlloc_1615_, 10, v_platformIndependent_1604_);
lean_ctor_set(v_reuseFailAlloc_1615_, 11, v_dynlibs_1606_);
lean_ctor_set(v_reuseFailAlloc_1615_, 12, v_plugins_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*13, v_buildType_1593_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*13 + 1, v_backend_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*13 + 2, v_precompileImports_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1615_, sizeof(void*)*13 + 4, v_allowNonModules_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1618_, lean_object* v_cfg_1619_){
_start:
{
uint8_t v_buildType_1620_; lean_object* v_leanOptions_1621_; lean_object* v_moreLeanArgs_1622_; lean_object* v_weakLeanArgs_1623_; lean_object* v_moreLeancArgs_1624_; lean_object* v_moreServerOptions_1625_; lean_object* v_weakLeancArgs_1626_; lean_object* v_moreLinkObjs_1627_; lean_object* v_moreLinkLibs_1628_; lean_object* v_moreLinkArgs_1629_; lean_object* v_weakLinkArgs_1630_; uint8_t v_backend_1631_; lean_object* v_platformIndependent_1632_; uint8_t v_precompileImports_1633_; lean_object* v_dynlibs_1634_; lean_object* v_plugins_1635_; uint8_t v_requiresModuleSystem_1636_; uint8_t v_allowNonModules_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1645_; 
v_buildType_1620_ = lean_ctor_get_uint8(v_cfg_1619_, sizeof(void*)*13);
v_leanOptions_1621_ = lean_ctor_get(v_cfg_1619_, 0);
v_moreLeanArgs_1622_ = lean_ctor_get(v_cfg_1619_, 1);
v_weakLeanArgs_1623_ = lean_ctor_get(v_cfg_1619_, 2);
v_moreLeancArgs_1624_ = lean_ctor_get(v_cfg_1619_, 3);
v_moreServerOptions_1625_ = lean_ctor_get(v_cfg_1619_, 4);
v_weakLeancArgs_1626_ = lean_ctor_get(v_cfg_1619_, 5);
v_moreLinkObjs_1627_ = lean_ctor_get(v_cfg_1619_, 6);
v_moreLinkLibs_1628_ = lean_ctor_get(v_cfg_1619_, 7);
v_moreLinkArgs_1629_ = lean_ctor_get(v_cfg_1619_, 8);
v_weakLinkArgs_1630_ = lean_ctor_get(v_cfg_1619_, 9);
v_backend_1631_ = lean_ctor_get_uint8(v_cfg_1619_, sizeof(void*)*13 + 1);
v_platformIndependent_1632_ = lean_ctor_get(v_cfg_1619_, 10);
v_precompileImports_1633_ = lean_ctor_get_uint8(v_cfg_1619_, sizeof(void*)*13 + 2);
v_dynlibs_1634_ = lean_ctor_get(v_cfg_1619_, 11);
v_plugins_1635_ = lean_ctor_get(v_cfg_1619_, 12);
v_requiresModuleSystem_1636_ = lean_ctor_get_uint8(v_cfg_1619_, sizeof(void*)*13 + 3);
v_allowNonModules_1637_ = lean_ctor_get_uint8(v_cfg_1619_, sizeof(void*)*13 + 4);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_cfg_1619_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1639_ = v_cfg_1619_;
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_plugins_1635_);
lean_inc(v_dynlibs_1634_);
lean_inc(v_platformIndependent_1632_);
lean_inc(v_weakLinkArgs_1630_);
lean_inc(v_moreLinkArgs_1629_);
lean_inc(v_moreLinkLibs_1628_);
lean_inc(v_moreLinkObjs_1627_);
lean_inc(v_weakLeancArgs_1626_);
lean_inc(v_moreServerOptions_1625_);
lean_inc(v_moreLeancArgs_1624_);
lean_inc(v_weakLeanArgs_1623_);
lean_inc(v_moreLeanArgs_1622_);
lean_inc(v_leanOptions_1621_);
lean_dec(v_cfg_1619_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1645_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = lean_apply_1(v_f_1618_, v_moreLinkObjs_1627_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 6, v___x_1641_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_leanOptions_1621_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_moreLeanArgs_1622_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_weakLeanArgs_1623_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_moreLeancArgs_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_moreServerOptions_1625_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_weakLeancArgs_1626_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_moreLinkLibs_1628_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_moreLinkArgs_1629_);
lean_ctor_set(v_reuseFailAlloc_1644_, 9, v_weakLinkArgs_1630_);
lean_ctor_set(v_reuseFailAlloc_1644_, 10, v_platformIndependent_1632_);
lean_ctor_set(v_reuseFailAlloc_1644_, 11, v_dynlibs_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 12, v_plugins_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1644_, sizeof(void*)*13, v_buildType_1620_);
lean_ctor_set_uint8(v_reuseFailAlloc_1644_, sizeof(void*)*13 + 1, v_backend_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1644_, sizeof(void*)*13 + 2, v_precompileImports_1633_);
lean_ctor_set_uint8(v_reuseFailAlloc_1644_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1636_);
lean_ctor_set_uint8(v_reuseFailAlloc_1644_, sizeof(void*)*13 + 4, v_allowNonModules_1637_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1650_);
lean_dec_ref(v_x_1650_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1663_){
_start:
{
lean_object* v_moreLinkLibs_1664_; 
v_moreLinkLibs_1664_ = lean_ctor_get(v_cfg_1663_, 7);
lean_inc_ref(v_moreLinkLibs_1664_);
return v_moreLinkLibs_1664_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1665_);
lean_dec_ref(v_cfg_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1667_, lean_object* v_cfg_1668_){
_start:
{
uint8_t v_buildType_1669_; lean_object* v_leanOptions_1670_; lean_object* v_moreLeanArgs_1671_; lean_object* v_weakLeanArgs_1672_; lean_object* v_moreLeancArgs_1673_; lean_object* v_moreServerOptions_1674_; lean_object* v_weakLeancArgs_1675_; lean_object* v_moreLinkObjs_1676_; lean_object* v_moreLinkArgs_1677_; lean_object* v_weakLinkArgs_1678_; uint8_t v_backend_1679_; lean_object* v_platformIndependent_1680_; uint8_t v_precompileImports_1681_; lean_object* v_dynlibs_1682_; lean_object* v_plugins_1683_; uint8_t v_requiresModuleSystem_1684_; uint8_t v_allowNonModules_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
v_buildType_1669_ = lean_ctor_get_uint8(v_cfg_1668_, sizeof(void*)*13);
v_leanOptions_1670_ = lean_ctor_get(v_cfg_1668_, 0);
v_moreLeanArgs_1671_ = lean_ctor_get(v_cfg_1668_, 1);
v_weakLeanArgs_1672_ = lean_ctor_get(v_cfg_1668_, 2);
v_moreLeancArgs_1673_ = lean_ctor_get(v_cfg_1668_, 3);
v_moreServerOptions_1674_ = lean_ctor_get(v_cfg_1668_, 4);
v_weakLeancArgs_1675_ = lean_ctor_get(v_cfg_1668_, 5);
v_moreLinkObjs_1676_ = lean_ctor_get(v_cfg_1668_, 6);
v_moreLinkArgs_1677_ = lean_ctor_get(v_cfg_1668_, 8);
v_weakLinkArgs_1678_ = lean_ctor_get(v_cfg_1668_, 9);
v_backend_1679_ = lean_ctor_get_uint8(v_cfg_1668_, sizeof(void*)*13 + 1);
v_platformIndependent_1680_ = lean_ctor_get(v_cfg_1668_, 10);
v_precompileImports_1681_ = lean_ctor_get_uint8(v_cfg_1668_, sizeof(void*)*13 + 2);
v_dynlibs_1682_ = lean_ctor_get(v_cfg_1668_, 11);
v_plugins_1683_ = lean_ctor_get(v_cfg_1668_, 12);
v_requiresModuleSystem_1684_ = lean_ctor_get_uint8(v_cfg_1668_, sizeof(void*)*13 + 3);
v_allowNonModules_1685_ = lean_ctor_get_uint8(v_cfg_1668_, sizeof(void*)*13 + 4);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_cfg_1668_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v_cfg_1668_, 7);
lean_dec(v_unused_1693_);
v___x_1687_ = v_cfg_1668_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_plugins_1683_);
lean_inc(v_dynlibs_1682_);
lean_inc(v_platformIndependent_1680_);
lean_inc(v_weakLinkArgs_1678_);
lean_inc(v_moreLinkArgs_1677_);
lean_inc(v_moreLinkObjs_1676_);
lean_inc(v_weakLeancArgs_1675_);
lean_inc(v_moreServerOptions_1674_);
lean_inc(v_moreLeancArgs_1673_);
lean_inc(v_weakLeanArgs_1672_);
lean_inc(v_moreLeanArgs_1671_);
lean_inc(v_leanOptions_1670_);
lean_dec(v_cfg_1668_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 7, v_val_1667_);
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_leanOptions_1670_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_moreLeanArgs_1671_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_weakLeanArgs_1672_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_moreLeancArgs_1673_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_moreServerOptions_1674_);
lean_ctor_set(v_reuseFailAlloc_1691_, 5, v_weakLeancArgs_1675_);
lean_ctor_set(v_reuseFailAlloc_1691_, 6, v_moreLinkObjs_1676_);
lean_ctor_set(v_reuseFailAlloc_1691_, 7, v_val_1667_);
lean_ctor_set(v_reuseFailAlloc_1691_, 8, v_moreLinkArgs_1677_);
lean_ctor_set(v_reuseFailAlloc_1691_, 9, v_weakLinkArgs_1678_);
lean_ctor_set(v_reuseFailAlloc_1691_, 10, v_platformIndependent_1680_);
lean_ctor_set(v_reuseFailAlloc_1691_, 11, v_dynlibs_1682_);
lean_ctor_set(v_reuseFailAlloc_1691_, 12, v_plugins_1683_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*13, v_buildType_1669_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*13 + 1, v_backend_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*13 + 2, v_precompileImports_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1691_, sizeof(void*)*13 + 4, v_allowNonModules_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1694_, lean_object* v_cfg_1695_){
_start:
{
uint8_t v_buildType_1696_; lean_object* v_leanOptions_1697_; lean_object* v_moreLeanArgs_1698_; lean_object* v_weakLeanArgs_1699_; lean_object* v_moreLeancArgs_1700_; lean_object* v_moreServerOptions_1701_; lean_object* v_weakLeancArgs_1702_; lean_object* v_moreLinkObjs_1703_; lean_object* v_moreLinkLibs_1704_; lean_object* v_moreLinkArgs_1705_; lean_object* v_weakLinkArgs_1706_; uint8_t v_backend_1707_; lean_object* v_platformIndependent_1708_; uint8_t v_precompileImports_1709_; lean_object* v_dynlibs_1710_; lean_object* v_plugins_1711_; uint8_t v_requiresModuleSystem_1712_; uint8_t v_allowNonModules_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1721_; 
v_buildType_1696_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*13);
v_leanOptions_1697_ = lean_ctor_get(v_cfg_1695_, 0);
v_moreLeanArgs_1698_ = lean_ctor_get(v_cfg_1695_, 1);
v_weakLeanArgs_1699_ = lean_ctor_get(v_cfg_1695_, 2);
v_moreLeancArgs_1700_ = lean_ctor_get(v_cfg_1695_, 3);
v_moreServerOptions_1701_ = lean_ctor_get(v_cfg_1695_, 4);
v_weakLeancArgs_1702_ = lean_ctor_get(v_cfg_1695_, 5);
v_moreLinkObjs_1703_ = lean_ctor_get(v_cfg_1695_, 6);
v_moreLinkLibs_1704_ = lean_ctor_get(v_cfg_1695_, 7);
v_moreLinkArgs_1705_ = lean_ctor_get(v_cfg_1695_, 8);
v_weakLinkArgs_1706_ = lean_ctor_get(v_cfg_1695_, 9);
v_backend_1707_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*13 + 1);
v_platformIndependent_1708_ = lean_ctor_get(v_cfg_1695_, 10);
v_precompileImports_1709_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*13 + 2);
v_dynlibs_1710_ = lean_ctor_get(v_cfg_1695_, 11);
v_plugins_1711_ = lean_ctor_get(v_cfg_1695_, 12);
v_requiresModuleSystem_1712_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*13 + 3);
v_allowNonModules_1713_ = lean_ctor_get_uint8(v_cfg_1695_, sizeof(void*)*13 + 4);
v_isSharedCheck_1721_ = !lean_is_exclusive(v_cfg_1695_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1715_ = v_cfg_1695_;
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_plugins_1711_);
lean_inc(v_dynlibs_1710_);
lean_inc(v_platformIndependent_1708_);
lean_inc(v_weakLinkArgs_1706_);
lean_inc(v_moreLinkArgs_1705_);
lean_inc(v_moreLinkLibs_1704_);
lean_inc(v_moreLinkObjs_1703_);
lean_inc(v_weakLeancArgs_1702_);
lean_inc(v_moreServerOptions_1701_);
lean_inc(v_moreLeancArgs_1700_);
lean_inc(v_weakLeanArgs_1699_);
lean_inc(v_moreLeanArgs_1698_);
lean_inc(v_leanOptions_1697_);
lean_dec(v_cfg_1695_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1721_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_apply_1(v_f_1694_, v_moreLinkLibs_1704_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 7, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_leanOptions_1697_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_moreLeanArgs_1698_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_weakLeanArgs_1699_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v_moreLeancArgs_1700_);
lean_ctor_set(v_reuseFailAlloc_1720_, 4, v_moreServerOptions_1701_);
lean_ctor_set(v_reuseFailAlloc_1720_, 5, v_weakLeancArgs_1702_);
lean_ctor_set(v_reuseFailAlloc_1720_, 6, v_moreLinkObjs_1703_);
lean_ctor_set(v_reuseFailAlloc_1720_, 7, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1720_, 8, v_moreLinkArgs_1705_);
lean_ctor_set(v_reuseFailAlloc_1720_, 9, v_weakLinkArgs_1706_);
lean_ctor_set(v_reuseFailAlloc_1720_, 10, v_platformIndependent_1708_);
lean_ctor_set(v_reuseFailAlloc_1720_, 11, v_dynlibs_1710_);
lean_ctor_set(v_reuseFailAlloc_1720_, 12, v_plugins_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*13, v_buildType_1696_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*13 + 1, v_backend_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*13 + 2, v_precompileImports_1709_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1712_);
lean_ctor_set_uint8(v_reuseFailAlloc_1720_, sizeof(void*)*13 + 4, v_allowNonModules_1713_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1732_){
_start:
{
lean_object* v_moreLinkArgs_1733_; 
v_moreLinkArgs_1733_ = lean_ctor_get(v_cfg_1732_, 8);
lean_inc_ref(v_moreLinkArgs_1733_);
return v_moreLinkArgs_1733_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1734_){
_start:
{
lean_object* v_res_1735_; 
v_res_1735_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1734_);
lean_dec_ref(v_cfg_1734_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1736_, lean_object* v_cfg_1737_){
_start:
{
uint8_t v_buildType_1738_; lean_object* v_leanOptions_1739_; lean_object* v_moreLeanArgs_1740_; lean_object* v_weakLeanArgs_1741_; lean_object* v_moreLeancArgs_1742_; lean_object* v_moreServerOptions_1743_; lean_object* v_weakLeancArgs_1744_; lean_object* v_moreLinkObjs_1745_; lean_object* v_moreLinkLibs_1746_; lean_object* v_weakLinkArgs_1747_; uint8_t v_backend_1748_; lean_object* v_platformIndependent_1749_; uint8_t v_precompileImports_1750_; lean_object* v_dynlibs_1751_; lean_object* v_plugins_1752_; uint8_t v_requiresModuleSystem_1753_; uint8_t v_allowNonModules_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_buildType_1738_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*13);
v_leanOptions_1739_ = lean_ctor_get(v_cfg_1737_, 0);
v_moreLeanArgs_1740_ = lean_ctor_get(v_cfg_1737_, 1);
v_weakLeanArgs_1741_ = lean_ctor_get(v_cfg_1737_, 2);
v_moreLeancArgs_1742_ = lean_ctor_get(v_cfg_1737_, 3);
v_moreServerOptions_1743_ = lean_ctor_get(v_cfg_1737_, 4);
v_weakLeancArgs_1744_ = lean_ctor_get(v_cfg_1737_, 5);
v_moreLinkObjs_1745_ = lean_ctor_get(v_cfg_1737_, 6);
v_moreLinkLibs_1746_ = lean_ctor_get(v_cfg_1737_, 7);
v_weakLinkArgs_1747_ = lean_ctor_get(v_cfg_1737_, 9);
v_backend_1748_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*13 + 1);
v_platformIndependent_1749_ = lean_ctor_get(v_cfg_1737_, 10);
v_precompileImports_1750_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*13 + 2);
v_dynlibs_1751_ = lean_ctor_get(v_cfg_1737_, 11);
v_plugins_1752_ = lean_ctor_get(v_cfg_1737_, 12);
v_requiresModuleSystem_1753_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*13 + 3);
v_allowNonModules_1754_ = lean_ctor_get_uint8(v_cfg_1737_, sizeof(void*)*13 + 4);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_cfg_1737_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; 
v_unused_1762_ = lean_ctor_get(v_cfg_1737_, 8);
lean_dec(v_unused_1762_);
v___x_1756_ = v_cfg_1737_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_plugins_1752_);
lean_inc(v_dynlibs_1751_);
lean_inc(v_platformIndependent_1749_);
lean_inc(v_weakLinkArgs_1747_);
lean_inc(v_moreLinkLibs_1746_);
lean_inc(v_moreLinkObjs_1745_);
lean_inc(v_weakLeancArgs_1744_);
lean_inc(v_moreServerOptions_1743_);
lean_inc(v_moreLeancArgs_1742_);
lean_inc(v_weakLeanArgs_1741_);
lean_inc(v_moreLeanArgs_1740_);
lean_inc(v_leanOptions_1739_);
lean_dec(v_cfg_1737_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 8, v_val_1736_);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_leanOptions_1739_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_moreLeanArgs_1740_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_weakLeanArgs_1741_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_moreLeancArgs_1742_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_moreServerOptions_1743_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v_weakLeancArgs_1744_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v_moreLinkObjs_1745_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_moreLinkLibs_1746_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v_val_1736_);
lean_ctor_set(v_reuseFailAlloc_1760_, 9, v_weakLinkArgs_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 10, v_platformIndependent_1749_);
lean_ctor_set(v_reuseFailAlloc_1760_, 11, v_dynlibs_1751_);
lean_ctor_set(v_reuseFailAlloc_1760_, 12, v_plugins_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13, v_buildType_1738_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13 + 1, v_backend_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13 + 2, v_precompileImports_1750_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1753_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13 + 4, v_allowNonModules_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1763_, lean_object* v_cfg_1764_){
_start:
{
uint8_t v_buildType_1765_; lean_object* v_leanOptions_1766_; lean_object* v_moreLeanArgs_1767_; lean_object* v_weakLeanArgs_1768_; lean_object* v_moreLeancArgs_1769_; lean_object* v_moreServerOptions_1770_; lean_object* v_weakLeancArgs_1771_; lean_object* v_moreLinkObjs_1772_; lean_object* v_moreLinkLibs_1773_; lean_object* v_moreLinkArgs_1774_; lean_object* v_weakLinkArgs_1775_; uint8_t v_backend_1776_; lean_object* v_platformIndependent_1777_; uint8_t v_precompileImports_1778_; lean_object* v_dynlibs_1779_; lean_object* v_plugins_1780_; uint8_t v_requiresModuleSystem_1781_; uint8_t v_allowNonModules_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1790_; 
v_buildType_1765_ = lean_ctor_get_uint8(v_cfg_1764_, sizeof(void*)*13);
v_leanOptions_1766_ = lean_ctor_get(v_cfg_1764_, 0);
v_moreLeanArgs_1767_ = lean_ctor_get(v_cfg_1764_, 1);
v_weakLeanArgs_1768_ = lean_ctor_get(v_cfg_1764_, 2);
v_moreLeancArgs_1769_ = lean_ctor_get(v_cfg_1764_, 3);
v_moreServerOptions_1770_ = lean_ctor_get(v_cfg_1764_, 4);
v_weakLeancArgs_1771_ = lean_ctor_get(v_cfg_1764_, 5);
v_moreLinkObjs_1772_ = lean_ctor_get(v_cfg_1764_, 6);
v_moreLinkLibs_1773_ = lean_ctor_get(v_cfg_1764_, 7);
v_moreLinkArgs_1774_ = lean_ctor_get(v_cfg_1764_, 8);
v_weakLinkArgs_1775_ = lean_ctor_get(v_cfg_1764_, 9);
v_backend_1776_ = lean_ctor_get_uint8(v_cfg_1764_, sizeof(void*)*13 + 1);
v_platformIndependent_1777_ = lean_ctor_get(v_cfg_1764_, 10);
v_precompileImports_1778_ = lean_ctor_get_uint8(v_cfg_1764_, sizeof(void*)*13 + 2);
v_dynlibs_1779_ = lean_ctor_get(v_cfg_1764_, 11);
v_plugins_1780_ = lean_ctor_get(v_cfg_1764_, 12);
v_requiresModuleSystem_1781_ = lean_ctor_get_uint8(v_cfg_1764_, sizeof(void*)*13 + 3);
v_allowNonModules_1782_ = lean_ctor_get_uint8(v_cfg_1764_, sizeof(void*)*13 + 4);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_cfg_1764_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1784_ = v_cfg_1764_;
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_plugins_1780_);
lean_inc(v_dynlibs_1779_);
lean_inc(v_platformIndependent_1777_);
lean_inc(v_weakLinkArgs_1775_);
lean_inc(v_moreLinkArgs_1774_);
lean_inc(v_moreLinkLibs_1773_);
lean_inc(v_moreLinkObjs_1772_);
lean_inc(v_weakLeancArgs_1771_);
lean_inc(v_moreServerOptions_1770_);
lean_inc(v_moreLeancArgs_1769_);
lean_inc(v_weakLeanArgs_1768_);
lean_inc(v_moreLeanArgs_1767_);
lean_inc(v_leanOptions_1766_);
lean_dec(v_cfg_1764_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1790_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1786_; lean_object* v___x_1788_; 
v___x_1786_ = lean_apply_1(v_f_1763_, v_moreLinkArgs_1774_);
if (v_isShared_1785_ == 0)
{
lean_ctor_set(v___x_1784_, 8, v___x_1786_);
v___x_1788_ = v___x_1784_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_leanOptions_1766_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_moreLeanArgs_1767_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_weakLeanArgs_1768_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_moreLeancArgs_1769_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_moreServerOptions_1770_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_weakLeancArgs_1771_);
lean_ctor_set(v_reuseFailAlloc_1789_, 6, v_moreLinkObjs_1772_);
lean_ctor_set(v_reuseFailAlloc_1789_, 7, v_moreLinkLibs_1773_);
lean_ctor_set(v_reuseFailAlloc_1789_, 8, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1789_, 9, v_weakLinkArgs_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 10, v_platformIndependent_1777_);
lean_ctor_set(v_reuseFailAlloc_1789_, 11, v_dynlibs_1779_);
lean_ctor_set(v_reuseFailAlloc_1789_, 12, v_plugins_1780_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13, v_buildType_1765_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 1, v_backend_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 2, v_precompileImports_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1789_, sizeof(void*)*13 + 4, v_allowNonModules_1782_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1801_){
_start:
{
lean_object* v_weakLinkArgs_1802_; 
v_weakLinkArgs_1802_ = lean_ctor_get(v_cfg_1801_, 9);
lean_inc_ref(v_weakLinkArgs_1802_);
return v_weakLinkArgs_1802_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1803_);
lean_dec_ref(v_cfg_1803_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1805_, lean_object* v_cfg_1806_){
_start:
{
uint8_t v_buildType_1807_; lean_object* v_leanOptions_1808_; lean_object* v_moreLeanArgs_1809_; lean_object* v_weakLeanArgs_1810_; lean_object* v_moreLeancArgs_1811_; lean_object* v_moreServerOptions_1812_; lean_object* v_weakLeancArgs_1813_; lean_object* v_moreLinkObjs_1814_; lean_object* v_moreLinkLibs_1815_; lean_object* v_moreLinkArgs_1816_; uint8_t v_backend_1817_; lean_object* v_platformIndependent_1818_; uint8_t v_precompileImports_1819_; lean_object* v_dynlibs_1820_; lean_object* v_plugins_1821_; uint8_t v_requiresModuleSystem_1822_; uint8_t v_allowNonModules_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
v_buildType_1807_ = lean_ctor_get_uint8(v_cfg_1806_, sizeof(void*)*13);
v_leanOptions_1808_ = lean_ctor_get(v_cfg_1806_, 0);
v_moreLeanArgs_1809_ = lean_ctor_get(v_cfg_1806_, 1);
v_weakLeanArgs_1810_ = lean_ctor_get(v_cfg_1806_, 2);
v_moreLeancArgs_1811_ = lean_ctor_get(v_cfg_1806_, 3);
v_moreServerOptions_1812_ = lean_ctor_get(v_cfg_1806_, 4);
v_weakLeancArgs_1813_ = lean_ctor_get(v_cfg_1806_, 5);
v_moreLinkObjs_1814_ = lean_ctor_get(v_cfg_1806_, 6);
v_moreLinkLibs_1815_ = lean_ctor_get(v_cfg_1806_, 7);
v_moreLinkArgs_1816_ = lean_ctor_get(v_cfg_1806_, 8);
v_backend_1817_ = lean_ctor_get_uint8(v_cfg_1806_, sizeof(void*)*13 + 1);
v_platformIndependent_1818_ = lean_ctor_get(v_cfg_1806_, 10);
v_precompileImports_1819_ = lean_ctor_get_uint8(v_cfg_1806_, sizeof(void*)*13 + 2);
v_dynlibs_1820_ = lean_ctor_get(v_cfg_1806_, 11);
v_plugins_1821_ = lean_ctor_get(v_cfg_1806_, 12);
v_requiresModuleSystem_1822_ = lean_ctor_get_uint8(v_cfg_1806_, sizeof(void*)*13 + 3);
v_allowNonModules_1823_ = lean_ctor_get_uint8(v_cfg_1806_, sizeof(void*)*13 + 4);
v_isSharedCheck_1830_ = !lean_is_exclusive(v_cfg_1806_);
if (v_isSharedCheck_1830_ == 0)
{
lean_object* v_unused_1831_; 
v_unused_1831_ = lean_ctor_get(v_cfg_1806_, 9);
lean_dec(v_unused_1831_);
v___x_1825_ = v_cfg_1806_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_plugins_1821_);
lean_inc(v_dynlibs_1820_);
lean_inc(v_platformIndependent_1818_);
lean_inc(v_moreLinkArgs_1816_);
lean_inc(v_moreLinkLibs_1815_);
lean_inc(v_moreLinkObjs_1814_);
lean_inc(v_weakLeancArgs_1813_);
lean_inc(v_moreServerOptions_1812_);
lean_inc(v_moreLeancArgs_1811_);
lean_inc(v_weakLeanArgs_1810_);
lean_inc(v_moreLeanArgs_1809_);
lean_inc(v_leanOptions_1808_);
lean_dec(v_cfg_1806_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 9, v_val_1805_);
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_leanOptions_1808_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_moreLeanArgs_1809_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_weakLeanArgs_1810_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v_moreLeancArgs_1811_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_moreServerOptions_1812_);
lean_ctor_set(v_reuseFailAlloc_1829_, 5, v_weakLeancArgs_1813_);
lean_ctor_set(v_reuseFailAlloc_1829_, 6, v_moreLinkObjs_1814_);
lean_ctor_set(v_reuseFailAlloc_1829_, 7, v_moreLinkLibs_1815_);
lean_ctor_set(v_reuseFailAlloc_1829_, 8, v_moreLinkArgs_1816_);
lean_ctor_set(v_reuseFailAlloc_1829_, 9, v_val_1805_);
lean_ctor_set(v_reuseFailAlloc_1829_, 10, v_platformIndependent_1818_);
lean_ctor_set(v_reuseFailAlloc_1829_, 11, v_dynlibs_1820_);
lean_ctor_set(v_reuseFailAlloc_1829_, 12, v_plugins_1821_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*13, v_buildType_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*13 + 1, v_backend_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*13 + 2, v_precompileImports_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1829_, sizeof(void*)*13 + 4, v_allowNonModules_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1832_, lean_object* v_cfg_1833_){
_start:
{
uint8_t v_buildType_1834_; lean_object* v_leanOptions_1835_; lean_object* v_moreLeanArgs_1836_; lean_object* v_weakLeanArgs_1837_; lean_object* v_moreLeancArgs_1838_; lean_object* v_moreServerOptions_1839_; lean_object* v_weakLeancArgs_1840_; lean_object* v_moreLinkObjs_1841_; lean_object* v_moreLinkLibs_1842_; lean_object* v_moreLinkArgs_1843_; lean_object* v_weakLinkArgs_1844_; uint8_t v_backend_1845_; lean_object* v_platformIndependent_1846_; uint8_t v_precompileImports_1847_; lean_object* v_dynlibs_1848_; lean_object* v_plugins_1849_; uint8_t v_requiresModuleSystem_1850_; uint8_t v_allowNonModules_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_buildType_1834_ = lean_ctor_get_uint8(v_cfg_1833_, sizeof(void*)*13);
v_leanOptions_1835_ = lean_ctor_get(v_cfg_1833_, 0);
v_moreLeanArgs_1836_ = lean_ctor_get(v_cfg_1833_, 1);
v_weakLeanArgs_1837_ = lean_ctor_get(v_cfg_1833_, 2);
v_moreLeancArgs_1838_ = lean_ctor_get(v_cfg_1833_, 3);
v_moreServerOptions_1839_ = lean_ctor_get(v_cfg_1833_, 4);
v_weakLeancArgs_1840_ = lean_ctor_get(v_cfg_1833_, 5);
v_moreLinkObjs_1841_ = lean_ctor_get(v_cfg_1833_, 6);
v_moreLinkLibs_1842_ = lean_ctor_get(v_cfg_1833_, 7);
v_moreLinkArgs_1843_ = lean_ctor_get(v_cfg_1833_, 8);
v_weakLinkArgs_1844_ = lean_ctor_get(v_cfg_1833_, 9);
v_backend_1845_ = lean_ctor_get_uint8(v_cfg_1833_, sizeof(void*)*13 + 1);
v_platformIndependent_1846_ = lean_ctor_get(v_cfg_1833_, 10);
v_precompileImports_1847_ = lean_ctor_get_uint8(v_cfg_1833_, sizeof(void*)*13 + 2);
v_dynlibs_1848_ = lean_ctor_get(v_cfg_1833_, 11);
v_plugins_1849_ = lean_ctor_get(v_cfg_1833_, 12);
v_requiresModuleSystem_1850_ = lean_ctor_get_uint8(v_cfg_1833_, sizeof(void*)*13 + 3);
v_allowNonModules_1851_ = lean_ctor_get_uint8(v_cfg_1833_, sizeof(void*)*13 + 4);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_cfg_1833_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v_cfg_1833_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_plugins_1849_);
lean_inc(v_dynlibs_1848_);
lean_inc(v_platformIndependent_1846_);
lean_inc(v_weakLinkArgs_1844_);
lean_inc(v_moreLinkArgs_1843_);
lean_inc(v_moreLinkLibs_1842_);
lean_inc(v_moreLinkObjs_1841_);
lean_inc(v_weakLeancArgs_1840_);
lean_inc(v_moreServerOptions_1839_);
lean_inc(v_moreLeancArgs_1838_);
lean_inc(v_weakLeanArgs_1837_);
lean_inc(v_moreLeanArgs_1836_);
lean_inc(v_leanOptions_1835_);
lean_dec(v_cfg_1833_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_apply_1(v_f_1832_, v_weakLinkArgs_1844_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 9, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_leanOptions_1835_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_moreLeanArgs_1836_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_weakLeanArgs_1837_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_moreLeancArgs_1838_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_moreServerOptions_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_weakLeancArgs_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_moreLinkObjs_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_moreLinkLibs_1842_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v_moreLinkArgs_1843_);
lean_ctor_set(v_reuseFailAlloc_1858_, 9, v___x_1855_);
lean_ctor_set(v_reuseFailAlloc_1858_, 10, v_platformIndependent_1846_);
lean_ctor_set(v_reuseFailAlloc_1858_, 11, v_dynlibs_1848_);
lean_ctor_set(v_reuseFailAlloc_1858_, 12, v_plugins_1849_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13, v_buildType_1834_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 1, v_backend_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 2, v_precompileImports_1847_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1850_);
lean_ctor_set_uint8(v_reuseFailAlloc_1858_, sizeof(void*)*13 + 4, v_allowNonModules_1851_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1870_){
_start:
{
uint8_t v_backend_1871_; 
v_backend_1871_ = lean_ctor_get_uint8(v_cfg_1870_, sizeof(void*)*13 + 1);
return v_backend_1871_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1872_){
_start:
{
uint8_t v_res_1873_; lean_object* v_r_1874_; 
v_res_1873_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1872_);
lean_dec_ref(v_cfg_1872_);
v_r_1874_ = lean_box(v_res_1873_);
return v_r_1874_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1875_, lean_object* v_cfg_1876_){
_start:
{
uint8_t v_buildType_1877_; lean_object* v_leanOptions_1878_; lean_object* v_moreLeanArgs_1879_; lean_object* v_weakLeanArgs_1880_; lean_object* v_moreLeancArgs_1881_; lean_object* v_moreServerOptions_1882_; lean_object* v_weakLeancArgs_1883_; lean_object* v_moreLinkObjs_1884_; lean_object* v_moreLinkLibs_1885_; lean_object* v_moreLinkArgs_1886_; lean_object* v_weakLinkArgs_1887_; lean_object* v_platformIndependent_1888_; uint8_t v_precompileImports_1889_; lean_object* v_dynlibs_1890_; lean_object* v_plugins_1891_; uint8_t v_requiresModuleSystem_1892_; uint8_t v_allowNonModules_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_buildType_1877_ = lean_ctor_get_uint8(v_cfg_1876_, sizeof(void*)*13);
v_leanOptions_1878_ = lean_ctor_get(v_cfg_1876_, 0);
v_moreLeanArgs_1879_ = lean_ctor_get(v_cfg_1876_, 1);
v_weakLeanArgs_1880_ = lean_ctor_get(v_cfg_1876_, 2);
v_moreLeancArgs_1881_ = lean_ctor_get(v_cfg_1876_, 3);
v_moreServerOptions_1882_ = lean_ctor_get(v_cfg_1876_, 4);
v_weakLeancArgs_1883_ = lean_ctor_get(v_cfg_1876_, 5);
v_moreLinkObjs_1884_ = lean_ctor_get(v_cfg_1876_, 6);
v_moreLinkLibs_1885_ = lean_ctor_get(v_cfg_1876_, 7);
v_moreLinkArgs_1886_ = lean_ctor_get(v_cfg_1876_, 8);
v_weakLinkArgs_1887_ = lean_ctor_get(v_cfg_1876_, 9);
v_platformIndependent_1888_ = lean_ctor_get(v_cfg_1876_, 10);
v_precompileImports_1889_ = lean_ctor_get_uint8(v_cfg_1876_, sizeof(void*)*13 + 2);
v_dynlibs_1890_ = lean_ctor_get(v_cfg_1876_, 11);
v_plugins_1891_ = lean_ctor_get(v_cfg_1876_, 12);
v_requiresModuleSystem_1892_ = lean_ctor_get_uint8(v_cfg_1876_, sizeof(void*)*13 + 3);
v_allowNonModules_1893_ = lean_ctor_get_uint8(v_cfg_1876_, sizeof(void*)*13 + 4);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_cfg_1876_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v_cfg_1876_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_plugins_1891_);
lean_inc(v_dynlibs_1890_);
lean_inc(v_platformIndependent_1888_);
lean_inc(v_weakLinkArgs_1887_);
lean_inc(v_moreLinkArgs_1886_);
lean_inc(v_moreLinkLibs_1885_);
lean_inc(v_moreLinkObjs_1884_);
lean_inc(v_weakLeancArgs_1883_);
lean_inc(v_moreServerOptions_1882_);
lean_inc(v_moreLeancArgs_1881_);
lean_inc(v_weakLeanArgs_1880_);
lean_inc(v_moreLeanArgs_1879_);
lean_inc(v_leanOptions_1878_);
lean_dec(v_cfg_1876_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_leanOptions_1878_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_moreLeanArgs_1879_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_weakLeanArgs_1880_);
lean_ctor_set(v_reuseFailAlloc_1899_, 3, v_moreLeancArgs_1881_);
lean_ctor_set(v_reuseFailAlloc_1899_, 4, v_moreServerOptions_1882_);
lean_ctor_set(v_reuseFailAlloc_1899_, 5, v_weakLeancArgs_1883_);
lean_ctor_set(v_reuseFailAlloc_1899_, 6, v_moreLinkObjs_1884_);
lean_ctor_set(v_reuseFailAlloc_1899_, 7, v_moreLinkLibs_1885_);
lean_ctor_set(v_reuseFailAlloc_1899_, 8, v_moreLinkArgs_1886_);
lean_ctor_set(v_reuseFailAlloc_1899_, 9, v_weakLinkArgs_1887_);
lean_ctor_set(v_reuseFailAlloc_1899_, 10, v_platformIndependent_1888_);
lean_ctor_set(v_reuseFailAlloc_1899_, 11, v_dynlibs_1890_);
lean_ctor_set(v_reuseFailAlloc_1899_, 12, v_plugins_1891_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*13, v_buildType_1877_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*13 + 2, v_precompileImports_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1892_);
lean_ctor_set_uint8(v_reuseFailAlloc_1899_, sizeof(void*)*13 + 4, v_allowNonModules_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_ctor_set_uint8(v___x_1898_, sizeof(void*)*13 + 1, v_val_1875_);
return v___x_1898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1901_, lean_object* v_cfg_1902_){
_start:
{
uint8_t v_val_88__boxed_1903_; lean_object* v_res_1904_; 
v_val_88__boxed_1903_ = lean_unbox(v_val_1901_);
v_res_1904_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_88__boxed_1903_, v_cfg_1902_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1905_, lean_object* v_cfg_1906_){
_start:
{
uint8_t v_buildType_1907_; lean_object* v_leanOptions_1908_; lean_object* v_moreLeanArgs_1909_; lean_object* v_weakLeanArgs_1910_; lean_object* v_moreLeancArgs_1911_; lean_object* v_moreServerOptions_1912_; lean_object* v_weakLeancArgs_1913_; lean_object* v_moreLinkObjs_1914_; lean_object* v_moreLinkLibs_1915_; lean_object* v_moreLinkArgs_1916_; lean_object* v_weakLinkArgs_1917_; uint8_t v_backend_1918_; lean_object* v_platformIndependent_1919_; uint8_t v_precompileImports_1920_; lean_object* v_dynlibs_1921_; lean_object* v_plugins_1922_; uint8_t v_requiresModuleSystem_1923_; uint8_t v_allowNonModules_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1934_; 
v_buildType_1907_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*13);
v_leanOptions_1908_ = lean_ctor_get(v_cfg_1906_, 0);
v_moreLeanArgs_1909_ = lean_ctor_get(v_cfg_1906_, 1);
v_weakLeanArgs_1910_ = lean_ctor_get(v_cfg_1906_, 2);
v_moreLeancArgs_1911_ = lean_ctor_get(v_cfg_1906_, 3);
v_moreServerOptions_1912_ = lean_ctor_get(v_cfg_1906_, 4);
v_weakLeancArgs_1913_ = lean_ctor_get(v_cfg_1906_, 5);
v_moreLinkObjs_1914_ = lean_ctor_get(v_cfg_1906_, 6);
v_moreLinkLibs_1915_ = lean_ctor_get(v_cfg_1906_, 7);
v_moreLinkArgs_1916_ = lean_ctor_get(v_cfg_1906_, 8);
v_weakLinkArgs_1917_ = lean_ctor_get(v_cfg_1906_, 9);
v_backend_1918_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*13 + 1);
v_platformIndependent_1919_ = lean_ctor_get(v_cfg_1906_, 10);
v_precompileImports_1920_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*13 + 2);
v_dynlibs_1921_ = lean_ctor_get(v_cfg_1906_, 11);
v_plugins_1922_ = lean_ctor_get(v_cfg_1906_, 12);
v_requiresModuleSystem_1923_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*13 + 3);
v_allowNonModules_1924_ = lean_ctor_get_uint8(v_cfg_1906_, sizeof(void*)*13 + 4);
v_isSharedCheck_1934_ = !lean_is_exclusive(v_cfg_1906_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1926_ = v_cfg_1906_;
v_isShared_1927_ = v_isSharedCheck_1934_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_plugins_1922_);
lean_inc(v_dynlibs_1921_);
lean_inc(v_platformIndependent_1919_);
lean_inc(v_weakLinkArgs_1917_);
lean_inc(v_moreLinkArgs_1916_);
lean_inc(v_moreLinkLibs_1915_);
lean_inc(v_moreLinkObjs_1914_);
lean_inc(v_weakLeancArgs_1913_);
lean_inc(v_moreServerOptions_1912_);
lean_inc(v_moreLeancArgs_1911_);
lean_inc(v_weakLeanArgs_1910_);
lean_inc(v_moreLeanArgs_1909_);
lean_inc(v_leanOptions_1908_);
lean_dec(v_cfg_1906_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1934_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1928_ = lean_box(v_backend_1918_);
v___x_1929_ = lean_apply_1(v_f_1905_, v___x_1928_);
if (v_isShared_1927_ == 0)
{
v___x_1931_ = v___x_1926_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_leanOptions_1908_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_moreLeanArgs_1909_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_weakLeanArgs_1910_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_moreLeancArgs_1911_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v_moreServerOptions_1912_);
lean_ctor_set(v_reuseFailAlloc_1933_, 5, v_weakLeancArgs_1913_);
lean_ctor_set(v_reuseFailAlloc_1933_, 6, v_moreLinkObjs_1914_);
lean_ctor_set(v_reuseFailAlloc_1933_, 7, v_moreLinkLibs_1915_);
lean_ctor_set(v_reuseFailAlloc_1933_, 8, v_moreLinkArgs_1916_);
lean_ctor_set(v_reuseFailAlloc_1933_, 9, v_weakLinkArgs_1917_);
lean_ctor_set(v_reuseFailAlloc_1933_, 10, v_platformIndependent_1919_);
lean_ctor_set(v_reuseFailAlloc_1933_, 11, v_dynlibs_1921_);
lean_ctor_set(v_reuseFailAlloc_1933_, 12, v_plugins_1922_);
lean_ctor_set_uint8(v_reuseFailAlloc_1933_, sizeof(void*)*13, v_buildType_1907_);
v___x_1931_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
uint8_t v___x_1932_; 
v___x_1932_ = lean_unbox(v___x_1929_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*13 + 1, v___x_1932_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*13 + 2, v_precompileImports_1920_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1923_);
lean_ctor_set_uint8(v___x_1931_, sizeof(void*)*13 + 4, v_allowNonModules_1924_);
return v___x_1931_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1935_){
_start:
{
uint8_t v___x_1936_; 
v___x_1936_ = 2;
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1937_){
_start:
{
uint8_t v_res_1938_; lean_object* v_r_1939_; 
v_res_1938_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1937_);
lean_dec_ref(v_x_1937_);
v_r_1939_ = lean_box(v_res_1938_);
return v_r_1939_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1951_){
_start:
{
lean_object* v_platformIndependent_1952_; 
v_platformIndependent_1952_ = lean_ctor_get(v_cfg_1951_, 10);
lean_inc(v_platformIndependent_1952_);
return v_platformIndependent_1952_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1953_);
lean_dec_ref(v_cfg_1953_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1955_, lean_object* v_cfg_1956_){
_start:
{
uint8_t v_buildType_1957_; lean_object* v_leanOptions_1958_; lean_object* v_moreLeanArgs_1959_; lean_object* v_weakLeanArgs_1960_; lean_object* v_moreLeancArgs_1961_; lean_object* v_moreServerOptions_1962_; lean_object* v_weakLeancArgs_1963_; lean_object* v_moreLinkObjs_1964_; lean_object* v_moreLinkLibs_1965_; lean_object* v_moreLinkArgs_1966_; lean_object* v_weakLinkArgs_1967_; uint8_t v_backend_1968_; uint8_t v_precompileImports_1969_; lean_object* v_dynlibs_1970_; lean_object* v_plugins_1971_; uint8_t v_requiresModuleSystem_1972_; uint8_t v_allowNonModules_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
v_buildType_1957_ = lean_ctor_get_uint8(v_cfg_1956_, sizeof(void*)*13);
v_leanOptions_1958_ = lean_ctor_get(v_cfg_1956_, 0);
v_moreLeanArgs_1959_ = lean_ctor_get(v_cfg_1956_, 1);
v_weakLeanArgs_1960_ = lean_ctor_get(v_cfg_1956_, 2);
v_moreLeancArgs_1961_ = lean_ctor_get(v_cfg_1956_, 3);
v_moreServerOptions_1962_ = lean_ctor_get(v_cfg_1956_, 4);
v_weakLeancArgs_1963_ = lean_ctor_get(v_cfg_1956_, 5);
v_moreLinkObjs_1964_ = lean_ctor_get(v_cfg_1956_, 6);
v_moreLinkLibs_1965_ = lean_ctor_get(v_cfg_1956_, 7);
v_moreLinkArgs_1966_ = lean_ctor_get(v_cfg_1956_, 8);
v_weakLinkArgs_1967_ = lean_ctor_get(v_cfg_1956_, 9);
v_backend_1968_ = lean_ctor_get_uint8(v_cfg_1956_, sizeof(void*)*13 + 1);
v_precompileImports_1969_ = lean_ctor_get_uint8(v_cfg_1956_, sizeof(void*)*13 + 2);
v_dynlibs_1970_ = lean_ctor_get(v_cfg_1956_, 11);
v_plugins_1971_ = lean_ctor_get(v_cfg_1956_, 12);
v_requiresModuleSystem_1972_ = lean_ctor_get_uint8(v_cfg_1956_, sizeof(void*)*13 + 3);
v_allowNonModules_1973_ = lean_ctor_get_uint8(v_cfg_1956_, sizeof(void*)*13 + 4);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_cfg_1956_);
if (v_isSharedCheck_1980_ == 0)
{
lean_object* v_unused_1981_; 
v_unused_1981_ = lean_ctor_get(v_cfg_1956_, 10);
lean_dec(v_unused_1981_);
v___x_1975_ = v_cfg_1956_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_plugins_1971_);
lean_inc(v_dynlibs_1970_);
lean_inc(v_weakLinkArgs_1967_);
lean_inc(v_moreLinkArgs_1966_);
lean_inc(v_moreLinkLibs_1965_);
lean_inc(v_moreLinkObjs_1964_);
lean_inc(v_weakLeancArgs_1963_);
lean_inc(v_moreServerOptions_1962_);
lean_inc(v_moreLeancArgs_1961_);
lean_inc(v_weakLeanArgs_1960_);
lean_inc(v_moreLeanArgs_1959_);
lean_inc(v_leanOptions_1958_);
lean_dec(v_cfg_1956_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 10, v_val_1955_);
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_leanOptions_1958_);
lean_ctor_set(v_reuseFailAlloc_1979_, 1, v_moreLeanArgs_1959_);
lean_ctor_set(v_reuseFailAlloc_1979_, 2, v_weakLeanArgs_1960_);
lean_ctor_set(v_reuseFailAlloc_1979_, 3, v_moreLeancArgs_1961_);
lean_ctor_set(v_reuseFailAlloc_1979_, 4, v_moreServerOptions_1962_);
lean_ctor_set(v_reuseFailAlloc_1979_, 5, v_weakLeancArgs_1963_);
lean_ctor_set(v_reuseFailAlloc_1979_, 6, v_moreLinkObjs_1964_);
lean_ctor_set(v_reuseFailAlloc_1979_, 7, v_moreLinkLibs_1965_);
lean_ctor_set(v_reuseFailAlloc_1979_, 8, v_moreLinkArgs_1966_);
lean_ctor_set(v_reuseFailAlloc_1979_, 9, v_weakLinkArgs_1967_);
lean_ctor_set(v_reuseFailAlloc_1979_, 10, v_val_1955_);
lean_ctor_set(v_reuseFailAlloc_1979_, 11, v_dynlibs_1970_);
lean_ctor_set(v_reuseFailAlloc_1979_, 12, v_plugins_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1979_, sizeof(void*)*13, v_buildType_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1979_, sizeof(void*)*13 + 1, v_backend_1968_);
lean_ctor_set_uint8(v_reuseFailAlloc_1979_, sizeof(void*)*13 + 2, v_precompileImports_1969_);
lean_ctor_set_uint8(v_reuseFailAlloc_1979_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1979_, sizeof(void*)*13 + 4, v_allowNonModules_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_1982_, lean_object* v_cfg_1983_){
_start:
{
uint8_t v_buildType_1984_; lean_object* v_leanOptions_1985_; lean_object* v_moreLeanArgs_1986_; lean_object* v_weakLeanArgs_1987_; lean_object* v_moreLeancArgs_1988_; lean_object* v_moreServerOptions_1989_; lean_object* v_weakLeancArgs_1990_; lean_object* v_moreLinkObjs_1991_; lean_object* v_moreLinkLibs_1992_; lean_object* v_moreLinkArgs_1993_; lean_object* v_weakLinkArgs_1994_; uint8_t v_backend_1995_; lean_object* v_platformIndependent_1996_; uint8_t v_precompileImports_1997_; lean_object* v_dynlibs_1998_; lean_object* v_plugins_1999_; uint8_t v_requiresModuleSystem_2000_; uint8_t v_allowNonModules_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2009_; 
v_buildType_1984_ = lean_ctor_get_uint8(v_cfg_1983_, sizeof(void*)*13);
v_leanOptions_1985_ = lean_ctor_get(v_cfg_1983_, 0);
v_moreLeanArgs_1986_ = lean_ctor_get(v_cfg_1983_, 1);
v_weakLeanArgs_1987_ = lean_ctor_get(v_cfg_1983_, 2);
v_moreLeancArgs_1988_ = lean_ctor_get(v_cfg_1983_, 3);
v_moreServerOptions_1989_ = lean_ctor_get(v_cfg_1983_, 4);
v_weakLeancArgs_1990_ = lean_ctor_get(v_cfg_1983_, 5);
v_moreLinkObjs_1991_ = lean_ctor_get(v_cfg_1983_, 6);
v_moreLinkLibs_1992_ = lean_ctor_get(v_cfg_1983_, 7);
v_moreLinkArgs_1993_ = lean_ctor_get(v_cfg_1983_, 8);
v_weakLinkArgs_1994_ = lean_ctor_get(v_cfg_1983_, 9);
v_backend_1995_ = lean_ctor_get_uint8(v_cfg_1983_, sizeof(void*)*13 + 1);
v_platformIndependent_1996_ = lean_ctor_get(v_cfg_1983_, 10);
v_precompileImports_1997_ = lean_ctor_get_uint8(v_cfg_1983_, sizeof(void*)*13 + 2);
v_dynlibs_1998_ = lean_ctor_get(v_cfg_1983_, 11);
v_plugins_1999_ = lean_ctor_get(v_cfg_1983_, 12);
v_requiresModuleSystem_2000_ = lean_ctor_get_uint8(v_cfg_1983_, sizeof(void*)*13 + 3);
v_allowNonModules_2001_ = lean_ctor_get_uint8(v_cfg_1983_, sizeof(void*)*13 + 4);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_cfg_1983_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2003_ = v_cfg_1983_;
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_plugins_1999_);
lean_inc(v_dynlibs_1998_);
lean_inc(v_platformIndependent_1996_);
lean_inc(v_weakLinkArgs_1994_);
lean_inc(v_moreLinkArgs_1993_);
lean_inc(v_moreLinkLibs_1992_);
lean_inc(v_moreLinkObjs_1991_);
lean_inc(v_weakLeancArgs_1990_);
lean_inc(v_moreServerOptions_1989_);
lean_inc(v_moreLeancArgs_1988_);
lean_inc(v_weakLeanArgs_1987_);
lean_inc(v_moreLeanArgs_1986_);
lean_inc(v_leanOptions_1985_);
lean_dec(v_cfg_1983_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2009_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_apply_1(v_f_1982_, v_platformIndependent_1996_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 10, v___x_2005_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_leanOptions_1985_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_moreLeanArgs_1986_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_weakLeanArgs_1987_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v_moreLeancArgs_1988_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_moreServerOptions_1989_);
lean_ctor_set(v_reuseFailAlloc_2008_, 5, v_weakLeancArgs_1990_);
lean_ctor_set(v_reuseFailAlloc_2008_, 6, v_moreLinkObjs_1991_);
lean_ctor_set(v_reuseFailAlloc_2008_, 7, v_moreLinkLibs_1992_);
lean_ctor_set(v_reuseFailAlloc_2008_, 8, v_moreLinkArgs_1993_);
lean_ctor_set(v_reuseFailAlloc_2008_, 9, v_weakLinkArgs_1994_);
lean_ctor_set(v_reuseFailAlloc_2008_, 10, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 11, v_dynlibs_1998_);
lean_ctor_set(v_reuseFailAlloc_2008_, 12, v_plugins_1999_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13, v_buildType_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13 + 1, v_backend_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13 + 2, v_precompileImports_1997_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2000_);
lean_ctor_set_uint8(v_reuseFailAlloc_2008_, sizeof(void*)*13 + 4, v_allowNonModules_2001_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_box(0);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_2012_);
lean_dec_ref(v_x_2012_);
return v_res_2013_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__0(lean_object* v_cfg_2025_){
_start:
{
uint8_t v_precompileImports_2026_; 
v_precompileImports_2026_ = lean_ctor_get_uint8(v_cfg_2025_, sizeof(void*)*13 + 2);
return v_precompileImports_2026_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__0___boxed(lean_object* v_cfg_2027_){
_start:
{
uint8_t v_res_2028_; lean_object* v_r_2029_; 
v_res_2028_ = l_Lake_LeanConfig_precompileImports___proj___lam__0(v_cfg_2027_);
lean_dec_ref(v_cfg_2027_);
v_r_2029_ = lean_box(v_res_2028_);
return v_r_2029_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1(uint8_t v_val_2030_, lean_object* v_cfg_2031_){
_start:
{
uint8_t v_buildType_2032_; lean_object* v_leanOptions_2033_; lean_object* v_moreLeanArgs_2034_; lean_object* v_weakLeanArgs_2035_; lean_object* v_moreLeancArgs_2036_; lean_object* v_moreServerOptions_2037_; lean_object* v_weakLeancArgs_2038_; lean_object* v_moreLinkObjs_2039_; lean_object* v_moreLinkLibs_2040_; lean_object* v_moreLinkArgs_2041_; lean_object* v_weakLinkArgs_2042_; uint8_t v_backend_2043_; lean_object* v_platformIndependent_2044_; lean_object* v_dynlibs_2045_; lean_object* v_plugins_2046_; uint8_t v_requiresModuleSystem_2047_; uint8_t v_allowNonModules_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
v_buildType_2032_ = lean_ctor_get_uint8(v_cfg_2031_, sizeof(void*)*13);
v_leanOptions_2033_ = lean_ctor_get(v_cfg_2031_, 0);
v_moreLeanArgs_2034_ = lean_ctor_get(v_cfg_2031_, 1);
v_weakLeanArgs_2035_ = lean_ctor_get(v_cfg_2031_, 2);
v_moreLeancArgs_2036_ = lean_ctor_get(v_cfg_2031_, 3);
v_moreServerOptions_2037_ = lean_ctor_get(v_cfg_2031_, 4);
v_weakLeancArgs_2038_ = lean_ctor_get(v_cfg_2031_, 5);
v_moreLinkObjs_2039_ = lean_ctor_get(v_cfg_2031_, 6);
v_moreLinkLibs_2040_ = lean_ctor_get(v_cfg_2031_, 7);
v_moreLinkArgs_2041_ = lean_ctor_get(v_cfg_2031_, 8);
v_weakLinkArgs_2042_ = lean_ctor_get(v_cfg_2031_, 9);
v_backend_2043_ = lean_ctor_get_uint8(v_cfg_2031_, sizeof(void*)*13 + 1);
v_platformIndependent_2044_ = lean_ctor_get(v_cfg_2031_, 10);
v_dynlibs_2045_ = lean_ctor_get(v_cfg_2031_, 11);
v_plugins_2046_ = lean_ctor_get(v_cfg_2031_, 12);
v_requiresModuleSystem_2047_ = lean_ctor_get_uint8(v_cfg_2031_, sizeof(void*)*13 + 3);
v_allowNonModules_2048_ = lean_ctor_get_uint8(v_cfg_2031_, sizeof(void*)*13 + 4);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_cfg_2031_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v_cfg_2031_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_plugins_2046_);
lean_inc(v_dynlibs_2045_);
lean_inc(v_platformIndependent_2044_);
lean_inc(v_weakLinkArgs_2042_);
lean_inc(v_moreLinkArgs_2041_);
lean_inc(v_moreLinkLibs_2040_);
lean_inc(v_moreLinkObjs_2039_);
lean_inc(v_weakLeancArgs_2038_);
lean_inc(v_moreServerOptions_2037_);
lean_inc(v_moreLeancArgs_2036_);
lean_inc(v_weakLeanArgs_2035_);
lean_inc(v_moreLeanArgs_2034_);
lean_inc(v_leanOptions_2033_);
lean_dec(v_cfg_2031_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_leanOptions_2033_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_moreLeanArgs_2034_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_weakLeanArgs_2035_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_moreLeancArgs_2036_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_moreServerOptions_2037_);
lean_ctor_set(v_reuseFailAlloc_2054_, 5, v_weakLeancArgs_2038_);
lean_ctor_set(v_reuseFailAlloc_2054_, 6, v_moreLinkObjs_2039_);
lean_ctor_set(v_reuseFailAlloc_2054_, 7, v_moreLinkLibs_2040_);
lean_ctor_set(v_reuseFailAlloc_2054_, 8, v_moreLinkArgs_2041_);
lean_ctor_set(v_reuseFailAlloc_2054_, 9, v_weakLinkArgs_2042_);
lean_ctor_set(v_reuseFailAlloc_2054_, 10, v_platformIndependent_2044_);
lean_ctor_set(v_reuseFailAlloc_2054_, 11, v_dynlibs_2045_);
lean_ctor_set(v_reuseFailAlloc_2054_, 12, v_plugins_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13, v_buildType_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 1, v_backend_2043_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2047_);
lean_ctor_set_uint8(v_reuseFailAlloc_2054_, sizeof(void*)*13 + 4, v_allowNonModules_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_ctor_set_uint8(v___x_2053_, sizeof(void*)*13 + 2, v_val_2030_);
return v___x_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1___boxed(lean_object* v_val_2056_, lean_object* v_cfg_2057_){
_start:
{
uint8_t v_val_88__boxed_2058_; lean_object* v_res_2059_; 
v_val_88__boxed_2058_ = lean_unbox(v_val_2056_);
v_res_2059_ = l_Lake_LeanConfig_precompileImports___proj___lam__1(v_val_88__boxed_2058_, v_cfg_2057_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__2(lean_object* v_f_2060_, lean_object* v_cfg_2061_){
_start:
{
uint8_t v_buildType_2062_; lean_object* v_leanOptions_2063_; lean_object* v_moreLeanArgs_2064_; lean_object* v_weakLeanArgs_2065_; lean_object* v_moreLeancArgs_2066_; lean_object* v_moreServerOptions_2067_; lean_object* v_weakLeancArgs_2068_; lean_object* v_moreLinkObjs_2069_; lean_object* v_moreLinkLibs_2070_; lean_object* v_moreLinkArgs_2071_; lean_object* v_weakLinkArgs_2072_; uint8_t v_backend_2073_; lean_object* v_platformIndependent_2074_; uint8_t v_precompileImports_2075_; lean_object* v_dynlibs_2076_; lean_object* v_plugins_2077_; uint8_t v_requiresModuleSystem_2078_; uint8_t v_allowNonModules_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2089_; 
v_buildType_2062_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*13);
v_leanOptions_2063_ = lean_ctor_get(v_cfg_2061_, 0);
v_moreLeanArgs_2064_ = lean_ctor_get(v_cfg_2061_, 1);
v_weakLeanArgs_2065_ = lean_ctor_get(v_cfg_2061_, 2);
v_moreLeancArgs_2066_ = lean_ctor_get(v_cfg_2061_, 3);
v_moreServerOptions_2067_ = lean_ctor_get(v_cfg_2061_, 4);
v_weakLeancArgs_2068_ = lean_ctor_get(v_cfg_2061_, 5);
v_moreLinkObjs_2069_ = lean_ctor_get(v_cfg_2061_, 6);
v_moreLinkLibs_2070_ = lean_ctor_get(v_cfg_2061_, 7);
v_moreLinkArgs_2071_ = lean_ctor_get(v_cfg_2061_, 8);
v_weakLinkArgs_2072_ = lean_ctor_get(v_cfg_2061_, 9);
v_backend_2073_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*13 + 1);
v_platformIndependent_2074_ = lean_ctor_get(v_cfg_2061_, 10);
v_precompileImports_2075_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*13 + 2);
v_dynlibs_2076_ = lean_ctor_get(v_cfg_2061_, 11);
v_plugins_2077_ = lean_ctor_get(v_cfg_2061_, 12);
v_requiresModuleSystem_2078_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*13 + 3);
v_allowNonModules_2079_ = lean_ctor_get_uint8(v_cfg_2061_, sizeof(void*)*13 + 4);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_cfg_2061_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2081_ = v_cfg_2061_;
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_plugins_2077_);
lean_inc(v_dynlibs_2076_);
lean_inc(v_platformIndependent_2074_);
lean_inc(v_weakLinkArgs_2072_);
lean_inc(v_moreLinkArgs_2071_);
lean_inc(v_moreLinkLibs_2070_);
lean_inc(v_moreLinkObjs_2069_);
lean_inc(v_weakLeancArgs_2068_);
lean_inc(v_moreServerOptions_2067_);
lean_inc(v_moreLeancArgs_2066_);
lean_inc(v_weakLeanArgs_2065_);
lean_inc(v_moreLeanArgs_2064_);
lean_inc(v_leanOptions_2063_);
lean_dec(v_cfg_2061_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2089_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2083_ = lean_box(v_precompileImports_2075_);
v___x_2084_ = lean_apply_1(v_f_2060_, v___x_2083_);
if (v_isShared_2082_ == 0)
{
v___x_2086_ = v___x_2081_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_leanOptions_2063_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_moreLeanArgs_2064_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_weakLeanArgs_2065_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_moreLeancArgs_2066_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_moreServerOptions_2067_);
lean_ctor_set(v_reuseFailAlloc_2088_, 5, v_weakLeancArgs_2068_);
lean_ctor_set(v_reuseFailAlloc_2088_, 6, v_moreLinkObjs_2069_);
lean_ctor_set(v_reuseFailAlloc_2088_, 7, v_moreLinkLibs_2070_);
lean_ctor_set(v_reuseFailAlloc_2088_, 8, v_moreLinkArgs_2071_);
lean_ctor_set(v_reuseFailAlloc_2088_, 9, v_weakLinkArgs_2072_);
lean_ctor_set(v_reuseFailAlloc_2088_, 10, v_platformIndependent_2074_);
lean_ctor_set(v_reuseFailAlloc_2088_, 11, v_dynlibs_2076_);
lean_ctor_set(v_reuseFailAlloc_2088_, 12, v_plugins_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*13, v_buildType_2062_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*13 + 1, v_backend_2073_);
v___x_2086_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_unbox(v___x_2084_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*13 + 2, v___x_2087_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2078_);
lean_ctor_set_uint8(v___x_2086_, sizeof(void*)*13 + 4, v_allowNonModules_2079_);
return v___x_2086_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__3(lean_object* v_x_2090_){
_start:
{
uint8_t v___x_2091_; 
v___x_2091_ = 0;
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__3___boxed(lean_object* v_x_2092_){
_start:
{
uint8_t v_res_2093_; lean_object* v_r_2094_; 
v_res_2093_ = l_Lake_LeanConfig_precompileImports___proj___lam__3(v_x_2092_);
lean_dec_ref(v_x_2092_);
v_r_2094_ = lean_box(v_res_2093_);
return v_r_2094_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_2106_){
_start:
{
lean_object* v_dynlibs_2107_; 
v_dynlibs_2107_ = lean_ctor_get(v_cfg_2106_, 11);
lean_inc_ref(v_dynlibs_2107_);
return v_dynlibs_2107_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_2108_);
lean_dec_ref(v_cfg_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_2110_, lean_object* v_cfg_2111_){
_start:
{
uint8_t v_buildType_2112_; lean_object* v_leanOptions_2113_; lean_object* v_moreLeanArgs_2114_; lean_object* v_weakLeanArgs_2115_; lean_object* v_moreLeancArgs_2116_; lean_object* v_moreServerOptions_2117_; lean_object* v_weakLeancArgs_2118_; lean_object* v_moreLinkObjs_2119_; lean_object* v_moreLinkLibs_2120_; lean_object* v_moreLinkArgs_2121_; lean_object* v_weakLinkArgs_2122_; uint8_t v_backend_2123_; lean_object* v_platformIndependent_2124_; uint8_t v_precompileImports_2125_; lean_object* v_plugins_2126_; uint8_t v_requiresModuleSystem_2127_; uint8_t v_allowNonModules_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
v_buildType_2112_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*13);
v_leanOptions_2113_ = lean_ctor_get(v_cfg_2111_, 0);
v_moreLeanArgs_2114_ = lean_ctor_get(v_cfg_2111_, 1);
v_weakLeanArgs_2115_ = lean_ctor_get(v_cfg_2111_, 2);
v_moreLeancArgs_2116_ = lean_ctor_get(v_cfg_2111_, 3);
v_moreServerOptions_2117_ = lean_ctor_get(v_cfg_2111_, 4);
v_weakLeancArgs_2118_ = lean_ctor_get(v_cfg_2111_, 5);
v_moreLinkObjs_2119_ = lean_ctor_get(v_cfg_2111_, 6);
v_moreLinkLibs_2120_ = lean_ctor_get(v_cfg_2111_, 7);
v_moreLinkArgs_2121_ = lean_ctor_get(v_cfg_2111_, 8);
v_weakLinkArgs_2122_ = lean_ctor_get(v_cfg_2111_, 9);
v_backend_2123_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*13 + 1);
v_platformIndependent_2124_ = lean_ctor_get(v_cfg_2111_, 10);
v_precompileImports_2125_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*13 + 2);
v_plugins_2126_ = lean_ctor_get(v_cfg_2111_, 12);
v_requiresModuleSystem_2127_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*13 + 3);
v_allowNonModules_2128_ = lean_ctor_get_uint8(v_cfg_2111_, sizeof(void*)*13 + 4);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_cfg_2111_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v_cfg_2111_, 11);
lean_dec(v_unused_2136_);
v___x_2130_ = v_cfg_2111_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_plugins_2126_);
lean_inc(v_platformIndependent_2124_);
lean_inc(v_weakLinkArgs_2122_);
lean_inc(v_moreLinkArgs_2121_);
lean_inc(v_moreLinkLibs_2120_);
lean_inc(v_moreLinkObjs_2119_);
lean_inc(v_weakLeancArgs_2118_);
lean_inc(v_moreServerOptions_2117_);
lean_inc(v_moreLeancArgs_2116_);
lean_inc(v_weakLeanArgs_2115_);
lean_inc(v_moreLeanArgs_2114_);
lean_inc(v_leanOptions_2113_);
lean_dec(v_cfg_2111_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 11, v_val_2110_);
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_leanOptions_2113_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v_moreLeanArgs_2114_);
lean_ctor_set(v_reuseFailAlloc_2134_, 2, v_weakLeanArgs_2115_);
lean_ctor_set(v_reuseFailAlloc_2134_, 3, v_moreLeancArgs_2116_);
lean_ctor_set(v_reuseFailAlloc_2134_, 4, v_moreServerOptions_2117_);
lean_ctor_set(v_reuseFailAlloc_2134_, 5, v_weakLeancArgs_2118_);
lean_ctor_set(v_reuseFailAlloc_2134_, 6, v_moreLinkObjs_2119_);
lean_ctor_set(v_reuseFailAlloc_2134_, 7, v_moreLinkLibs_2120_);
lean_ctor_set(v_reuseFailAlloc_2134_, 8, v_moreLinkArgs_2121_);
lean_ctor_set(v_reuseFailAlloc_2134_, 9, v_weakLinkArgs_2122_);
lean_ctor_set(v_reuseFailAlloc_2134_, 10, v_platformIndependent_2124_);
lean_ctor_set(v_reuseFailAlloc_2134_, 11, v_val_2110_);
lean_ctor_set(v_reuseFailAlloc_2134_, 12, v_plugins_2126_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*13, v_buildType_2112_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*13 + 1, v_backend_2123_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*13 + 2, v_precompileImports_2125_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2127_);
lean_ctor_set_uint8(v_reuseFailAlloc_2134_, sizeof(void*)*13 + 4, v_allowNonModules_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_2137_, lean_object* v_cfg_2138_){
_start:
{
uint8_t v_buildType_2139_; lean_object* v_leanOptions_2140_; lean_object* v_moreLeanArgs_2141_; lean_object* v_weakLeanArgs_2142_; lean_object* v_moreLeancArgs_2143_; lean_object* v_moreServerOptions_2144_; lean_object* v_weakLeancArgs_2145_; lean_object* v_moreLinkObjs_2146_; lean_object* v_moreLinkLibs_2147_; lean_object* v_moreLinkArgs_2148_; lean_object* v_weakLinkArgs_2149_; uint8_t v_backend_2150_; lean_object* v_platformIndependent_2151_; uint8_t v_precompileImports_2152_; lean_object* v_dynlibs_2153_; lean_object* v_plugins_2154_; uint8_t v_requiresModuleSystem_2155_; uint8_t v_allowNonModules_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2164_; 
v_buildType_2139_ = lean_ctor_get_uint8(v_cfg_2138_, sizeof(void*)*13);
v_leanOptions_2140_ = lean_ctor_get(v_cfg_2138_, 0);
v_moreLeanArgs_2141_ = lean_ctor_get(v_cfg_2138_, 1);
v_weakLeanArgs_2142_ = lean_ctor_get(v_cfg_2138_, 2);
v_moreLeancArgs_2143_ = lean_ctor_get(v_cfg_2138_, 3);
v_moreServerOptions_2144_ = lean_ctor_get(v_cfg_2138_, 4);
v_weakLeancArgs_2145_ = lean_ctor_get(v_cfg_2138_, 5);
v_moreLinkObjs_2146_ = lean_ctor_get(v_cfg_2138_, 6);
v_moreLinkLibs_2147_ = lean_ctor_get(v_cfg_2138_, 7);
v_moreLinkArgs_2148_ = lean_ctor_get(v_cfg_2138_, 8);
v_weakLinkArgs_2149_ = lean_ctor_get(v_cfg_2138_, 9);
v_backend_2150_ = lean_ctor_get_uint8(v_cfg_2138_, sizeof(void*)*13 + 1);
v_platformIndependent_2151_ = lean_ctor_get(v_cfg_2138_, 10);
v_precompileImports_2152_ = lean_ctor_get_uint8(v_cfg_2138_, sizeof(void*)*13 + 2);
v_dynlibs_2153_ = lean_ctor_get(v_cfg_2138_, 11);
v_plugins_2154_ = lean_ctor_get(v_cfg_2138_, 12);
v_requiresModuleSystem_2155_ = lean_ctor_get_uint8(v_cfg_2138_, sizeof(void*)*13 + 3);
v_allowNonModules_2156_ = lean_ctor_get_uint8(v_cfg_2138_, sizeof(void*)*13 + 4);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_cfg_2138_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2158_ = v_cfg_2138_;
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_plugins_2154_);
lean_inc(v_dynlibs_2153_);
lean_inc(v_platformIndependent_2151_);
lean_inc(v_weakLinkArgs_2149_);
lean_inc(v_moreLinkArgs_2148_);
lean_inc(v_moreLinkLibs_2147_);
lean_inc(v_moreLinkObjs_2146_);
lean_inc(v_weakLeancArgs_2145_);
lean_inc(v_moreServerOptions_2144_);
lean_inc(v_moreLeancArgs_2143_);
lean_inc(v_weakLeanArgs_2142_);
lean_inc(v_moreLeanArgs_2141_);
lean_inc(v_leanOptions_2140_);
lean_dec(v_cfg_2138_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_apply_1(v_f_2137_, v_dynlibs_2153_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 11, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_leanOptions_2140_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_moreLeanArgs_2141_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_weakLeanArgs_2142_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v_moreLeancArgs_2143_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_moreServerOptions_2144_);
lean_ctor_set(v_reuseFailAlloc_2163_, 5, v_weakLeancArgs_2145_);
lean_ctor_set(v_reuseFailAlloc_2163_, 6, v_moreLinkObjs_2146_);
lean_ctor_set(v_reuseFailAlloc_2163_, 7, v_moreLinkLibs_2147_);
lean_ctor_set(v_reuseFailAlloc_2163_, 8, v_moreLinkArgs_2148_);
lean_ctor_set(v_reuseFailAlloc_2163_, 9, v_weakLinkArgs_2149_);
lean_ctor_set(v_reuseFailAlloc_2163_, 10, v_platformIndependent_2151_);
lean_ctor_set(v_reuseFailAlloc_2163_, 11, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2163_, 12, v_plugins_2154_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13, v_buildType_2139_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 1, v_backend_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 2, v_precompileImports_2152_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2155_);
lean_ctor_set_uint8(v_reuseFailAlloc_2163_, sizeof(void*)*13 + 4, v_allowNonModules_2156_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_2175_){
_start:
{
lean_object* v_plugins_2176_; 
v_plugins_2176_ = lean_ctor_get(v_cfg_2175_, 12);
lean_inc_ref(v_plugins_2176_);
return v_plugins_2176_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_2177_){
_start:
{
lean_object* v_res_2178_; 
v_res_2178_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_2177_);
lean_dec_ref(v_cfg_2177_);
return v_res_2178_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_2179_, lean_object* v_cfg_2180_){
_start:
{
uint8_t v_buildType_2181_; lean_object* v_leanOptions_2182_; lean_object* v_moreLeanArgs_2183_; lean_object* v_weakLeanArgs_2184_; lean_object* v_moreLeancArgs_2185_; lean_object* v_moreServerOptions_2186_; lean_object* v_weakLeancArgs_2187_; lean_object* v_moreLinkObjs_2188_; lean_object* v_moreLinkLibs_2189_; lean_object* v_moreLinkArgs_2190_; lean_object* v_weakLinkArgs_2191_; uint8_t v_backend_2192_; lean_object* v_platformIndependent_2193_; uint8_t v_precompileImports_2194_; lean_object* v_dynlibs_2195_; uint8_t v_requiresModuleSystem_2196_; uint8_t v_allowNonModules_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
v_buildType_2181_ = lean_ctor_get_uint8(v_cfg_2180_, sizeof(void*)*13);
v_leanOptions_2182_ = lean_ctor_get(v_cfg_2180_, 0);
v_moreLeanArgs_2183_ = lean_ctor_get(v_cfg_2180_, 1);
v_weakLeanArgs_2184_ = lean_ctor_get(v_cfg_2180_, 2);
v_moreLeancArgs_2185_ = lean_ctor_get(v_cfg_2180_, 3);
v_moreServerOptions_2186_ = lean_ctor_get(v_cfg_2180_, 4);
v_weakLeancArgs_2187_ = lean_ctor_get(v_cfg_2180_, 5);
v_moreLinkObjs_2188_ = lean_ctor_get(v_cfg_2180_, 6);
v_moreLinkLibs_2189_ = lean_ctor_get(v_cfg_2180_, 7);
v_moreLinkArgs_2190_ = lean_ctor_get(v_cfg_2180_, 8);
v_weakLinkArgs_2191_ = lean_ctor_get(v_cfg_2180_, 9);
v_backend_2192_ = lean_ctor_get_uint8(v_cfg_2180_, sizeof(void*)*13 + 1);
v_platformIndependent_2193_ = lean_ctor_get(v_cfg_2180_, 10);
v_precompileImports_2194_ = lean_ctor_get_uint8(v_cfg_2180_, sizeof(void*)*13 + 2);
v_dynlibs_2195_ = lean_ctor_get(v_cfg_2180_, 11);
v_requiresModuleSystem_2196_ = lean_ctor_get_uint8(v_cfg_2180_, sizeof(void*)*13 + 3);
v_allowNonModules_2197_ = lean_ctor_get_uint8(v_cfg_2180_, sizeof(void*)*13 + 4);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_cfg_2180_);
if (v_isSharedCheck_2204_ == 0)
{
lean_object* v_unused_2205_; 
v_unused_2205_ = lean_ctor_get(v_cfg_2180_, 12);
lean_dec(v_unused_2205_);
v___x_2199_ = v_cfg_2180_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_dynlibs_2195_);
lean_inc(v_platformIndependent_2193_);
lean_inc(v_weakLinkArgs_2191_);
lean_inc(v_moreLinkArgs_2190_);
lean_inc(v_moreLinkLibs_2189_);
lean_inc(v_moreLinkObjs_2188_);
lean_inc(v_weakLeancArgs_2187_);
lean_inc(v_moreServerOptions_2186_);
lean_inc(v_moreLeancArgs_2185_);
lean_inc(v_weakLeanArgs_2184_);
lean_inc(v_moreLeanArgs_2183_);
lean_inc(v_leanOptions_2182_);
lean_dec(v_cfg_2180_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 12, v_val_2179_);
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_leanOptions_2182_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_moreLeanArgs_2183_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_weakLeanArgs_2184_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_moreLeancArgs_2185_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v_moreServerOptions_2186_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_weakLeancArgs_2187_);
lean_ctor_set(v_reuseFailAlloc_2203_, 6, v_moreLinkObjs_2188_);
lean_ctor_set(v_reuseFailAlloc_2203_, 7, v_moreLinkLibs_2189_);
lean_ctor_set(v_reuseFailAlloc_2203_, 8, v_moreLinkArgs_2190_);
lean_ctor_set(v_reuseFailAlloc_2203_, 9, v_weakLinkArgs_2191_);
lean_ctor_set(v_reuseFailAlloc_2203_, 10, v_platformIndependent_2193_);
lean_ctor_set(v_reuseFailAlloc_2203_, 11, v_dynlibs_2195_);
lean_ctor_set(v_reuseFailAlloc_2203_, 12, v_val_2179_);
lean_ctor_set_uint8(v_reuseFailAlloc_2203_, sizeof(void*)*13, v_buildType_2181_);
lean_ctor_set_uint8(v_reuseFailAlloc_2203_, sizeof(void*)*13 + 1, v_backend_2192_);
lean_ctor_set_uint8(v_reuseFailAlloc_2203_, sizeof(void*)*13 + 2, v_precompileImports_2194_);
lean_ctor_set_uint8(v_reuseFailAlloc_2203_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2196_);
lean_ctor_set_uint8(v_reuseFailAlloc_2203_, sizeof(void*)*13 + 4, v_allowNonModules_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_2206_, lean_object* v_cfg_2207_){
_start:
{
uint8_t v_buildType_2208_; lean_object* v_leanOptions_2209_; lean_object* v_moreLeanArgs_2210_; lean_object* v_weakLeanArgs_2211_; lean_object* v_moreLeancArgs_2212_; lean_object* v_moreServerOptions_2213_; lean_object* v_weakLeancArgs_2214_; lean_object* v_moreLinkObjs_2215_; lean_object* v_moreLinkLibs_2216_; lean_object* v_moreLinkArgs_2217_; lean_object* v_weakLinkArgs_2218_; uint8_t v_backend_2219_; lean_object* v_platformIndependent_2220_; uint8_t v_precompileImports_2221_; lean_object* v_dynlibs_2222_; lean_object* v_plugins_2223_; uint8_t v_requiresModuleSystem_2224_; uint8_t v_allowNonModules_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_buildType_2208_ = lean_ctor_get_uint8(v_cfg_2207_, sizeof(void*)*13);
v_leanOptions_2209_ = lean_ctor_get(v_cfg_2207_, 0);
v_moreLeanArgs_2210_ = lean_ctor_get(v_cfg_2207_, 1);
v_weakLeanArgs_2211_ = lean_ctor_get(v_cfg_2207_, 2);
v_moreLeancArgs_2212_ = lean_ctor_get(v_cfg_2207_, 3);
v_moreServerOptions_2213_ = lean_ctor_get(v_cfg_2207_, 4);
v_weakLeancArgs_2214_ = lean_ctor_get(v_cfg_2207_, 5);
v_moreLinkObjs_2215_ = lean_ctor_get(v_cfg_2207_, 6);
v_moreLinkLibs_2216_ = lean_ctor_get(v_cfg_2207_, 7);
v_moreLinkArgs_2217_ = lean_ctor_get(v_cfg_2207_, 8);
v_weakLinkArgs_2218_ = lean_ctor_get(v_cfg_2207_, 9);
v_backend_2219_ = lean_ctor_get_uint8(v_cfg_2207_, sizeof(void*)*13 + 1);
v_platformIndependent_2220_ = lean_ctor_get(v_cfg_2207_, 10);
v_precompileImports_2221_ = lean_ctor_get_uint8(v_cfg_2207_, sizeof(void*)*13 + 2);
v_dynlibs_2222_ = lean_ctor_get(v_cfg_2207_, 11);
v_plugins_2223_ = lean_ctor_get(v_cfg_2207_, 12);
v_requiresModuleSystem_2224_ = lean_ctor_get_uint8(v_cfg_2207_, sizeof(void*)*13 + 3);
v_allowNonModules_2225_ = lean_ctor_get_uint8(v_cfg_2207_, sizeof(void*)*13 + 4);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_cfg_2207_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2227_ = v_cfg_2207_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_plugins_2223_);
lean_inc(v_dynlibs_2222_);
lean_inc(v_platformIndependent_2220_);
lean_inc(v_weakLinkArgs_2218_);
lean_inc(v_moreLinkArgs_2217_);
lean_inc(v_moreLinkLibs_2216_);
lean_inc(v_moreLinkObjs_2215_);
lean_inc(v_weakLeancArgs_2214_);
lean_inc(v_moreServerOptions_2213_);
lean_inc(v_moreLeancArgs_2212_);
lean_inc(v_weakLeanArgs_2211_);
lean_inc(v_moreLeanArgs_2210_);
lean_inc(v_leanOptions_2209_);
lean_dec(v_cfg_2207_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_apply_1(v_f_2206_, v_plugins_2223_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 12, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_leanOptions_2209_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_moreLeanArgs_2210_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_weakLeanArgs_2211_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_moreLeancArgs_2212_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_moreServerOptions_2213_);
lean_ctor_set(v_reuseFailAlloc_2232_, 5, v_weakLeancArgs_2214_);
lean_ctor_set(v_reuseFailAlloc_2232_, 6, v_moreLinkObjs_2215_);
lean_ctor_set(v_reuseFailAlloc_2232_, 7, v_moreLinkLibs_2216_);
lean_ctor_set(v_reuseFailAlloc_2232_, 8, v_moreLinkArgs_2217_);
lean_ctor_set(v_reuseFailAlloc_2232_, 9, v_weakLinkArgs_2218_);
lean_ctor_set(v_reuseFailAlloc_2232_, 10, v_platformIndependent_2220_);
lean_ctor_set(v_reuseFailAlloc_2232_, 11, v_dynlibs_2222_);
lean_ctor_set(v_reuseFailAlloc_2232_, 12, v___x_2229_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13, v_buildType_2208_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 1, v_backend_2219_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 2, v_precompileImports_2221_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2224_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13 + 4, v_allowNonModules_2225_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object* v_cfg_2244_){
_start:
{
uint8_t v_requiresModuleSystem_2245_; 
v_requiresModuleSystem_2245_ = lean_ctor_get_uint8(v_cfg_2244_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_2245_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object* v_cfg_2246_){
_start:
{
uint8_t v_res_2247_; lean_object* v_r_2248_; 
v_res_2247_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2246_);
lean_dec_ref(v_cfg_2246_);
v_r_2248_ = lean_box(v_res_2247_);
return v_r_2248_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t v_val_2249_, lean_object* v_cfg_2250_){
_start:
{
uint8_t v_buildType_2251_; lean_object* v_leanOptions_2252_; lean_object* v_moreLeanArgs_2253_; lean_object* v_weakLeanArgs_2254_; lean_object* v_moreLeancArgs_2255_; lean_object* v_moreServerOptions_2256_; lean_object* v_weakLeancArgs_2257_; lean_object* v_moreLinkObjs_2258_; lean_object* v_moreLinkLibs_2259_; lean_object* v_moreLinkArgs_2260_; lean_object* v_weakLinkArgs_2261_; uint8_t v_backend_2262_; lean_object* v_platformIndependent_2263_; uint8_t v_precompileImports_2264_; lean_object* v_dynlibs_2265_; lean_object* v_plugins_2266_; uint8_t v_allowNonModules_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_buildType_2251_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*13);
v_leanOptions_2252_ = lean_ctor_get(v_cfg_2250_, 0);
v_moreLeanArgs_2253_ = lean_ctor_get(v_cfg_2250_, 1);
v_weakLeanArgs_2254_ = lean_ctor_get(v_cfg_2250_, 2);
v_moreLeancArgs_2255_ = lean_ctor_get(v_cfg_2250_, 3);
v_moreServerOptions_2256_ = lean_ctor_get(v_cfg_2250_, 4);
v_weakLeancArgs_2257_ = lean_ctor_get(v_cfg_2250_, 5);
v_moreLinkObjs_2258_ = lean_ctor_get(v_cfg_2250_, 6);
v_moreLinkLibs_2259_ = lean_ctor_get(v_cfg_2250_, 7);
v_moreLinkArgs_2260_ = lean_ctor_get(v_cfg_2250_, 8);
v_weakLinkArgs_2261_ = lean_ctor_get(v_cfg_2250_, 9);
v_backend_2262_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*13 + 1);
v_platformIndependent_2263_ = lean_ctor_get(v_cfg_2250_, 10);
v_precompileImports_2264_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*13 + 2);
v_dynlibs_2265_ = lean_ctor_get(v_cfg_2250_, 11);
v_plugins_2266_ = lean_ctor_get(v_cfg_2250_, 12);
v_allowNonModules_2267_ = lean_ctor_get_uint8(v_cfg_2250_, sizeof(void*)*13 + 4);
v_isSharedCheck_2274_ = !lean_is_exclusive(v_cfg_2250_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v_cfg_2250_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_plugins_2266_);
lean_inc(v_dynlibs_2265_);
lean_inc(v_platformIndependent_2263_);
lean_inc(v_weakLinkArgs_2261_);
lean_inc(v_moreLinkArgs_2260_);
lean_inc(v_moreLinkLibs_2259_);
lean_inc(v_moreLinkObjs_2258_);
lean_inc(v_weakLeancArgs_2257_);
lean_inc(v_moreServerOptions_2256_);
lean_inc(v_moreLeancArgs_2255_);
lean_inc(v_weakLeanArgs_2254_);
lean_inc(v_moreLeanArgs_2253_);
lean_inc(v_leanOptions_2252_);
lean_dec(v_cfg_2250_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_leanOptions_2252_);
lean_ctor_set(v_reuseFailAlloc_2273_, 1, v_moreLeanArgs_2253_);
lean_ctor_set(v_reuseFailAlloc_2273_, 2, v_weakLeanArgs_2254_);
lean_ctor_set(v_reuseFailAlloc_2273_, 3, v_moreLeancArgs_2255_);
lean_ctor_set(v_reuseFailAlloc_2273_, 4, v_moreServerOptions_2256_);
lean_ctor_set(v_reuseFailAlloc_2273_, 5, v_weakLeancArgs_2257_);
lean_ctor_set(v_reuseFailAlloc_2273_, 6, v_moreLinkObjs_2258_);
lean_ctor_set(v_reuseFailAlloc_2273_, 7, v_moreLinkLibs_2259_);
lean_ctor_set(v_reuseFailAlloc_2273_, 8, v_moreLinkArgs_2260_);
lean_ctor_set(v_reuseFailAlloc_2273_, 9, v_weakLinkArgs_2261_);
lean_ctor_set(v_reuseFailAlloc_2273_, 10, v_platformIndependent_2263_);
lean_ctor_set(v_reuseFailAlloc_2273_, 11, v_dynlibs_2265_);
lean_ctor_set(v_reuseFailAlloc_2273_, 12, v_plugins_2266_);
lean_ctor_set_uint8(v_reuseFailAlloc_2273_, sizeof(void*)*13, v_buildType_2251_);
lean_ctor_set_uint8(v_reuseFailAlloc_2273_, sizeof(void*)*13 + 1, v_backend_2262_);
lean_ctor_set_uint8(v_reuseFailAlloc_2273_, sizeof(void*)*13 + 2, v_precompileImports_2264_);
lean_ctor_set_uint8(v_reuseFailAlloc_2273_, sizeof(void*)*13 + 4, v_allowNonModules_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*13 + 3, v_val_2249_);
return v___x_2272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object* v_val_2275_, lean_object* v_cfg_2276_){
_start:
{
uint8_t v_val_88__boxed_2277_; lean_object* v_res_2278_; 
v_val_88__boxed_2277_ = lean_unbox(v_val_2275_);
v_res_2278_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_88__boxed_2277_, v_cfg_2276_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object* v_f_2279_, lean_object* v_cfg_2280_){
_start:
{
uint8_t v_buildType_2281_; lean_object* v_leanOptions_2282_; lean_object* v_moreLeanArgs_2283_; lean_object* v_weakLeanArgs_2284_; lean_object* v_moreLeancArgs_2285_; lean_object* v_moreServerOptions_2286_; lean_object* v_weakLeancArgs_2287_; lean_object* v_moreLinkObjs_2288_; lean_object* v_moreLinkLibs_2289_; lean_object* v_moreLinkArgs_2290_; lean_object* v_weakLinkArgs_2291_; uint8_t v_backend_2292_; lean_object* v_platformIndependent_2293_; uint8_t v_precompileImports_2294_; lean_object* v_dynlibs_2295_; lean_object* v_plugins_2296_; uint8_t v_requiresModuleSystem_2297_; uint8_t v_allowNonModules_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2308_; 
v_buildType_2281_ = lean_ctor_get_uint8(v_cfg_2280_, sizeof(void*)*13);
v_leanOptions_2282_ = lean_ctor_get(v_cfg_2280_, 0);
v_moreLeanArgs_2283_ = lean_ctor_get(v_cfg_2280_, 1);
v_weakLeanArgs_2284_ = lean_ctor_get(v_cfg_2280_, 2);
v_moreLeancArgs_2285_ = lean_ctor_get(v_cfg_2280_, 3);
v_moreServerOptions_2286_ = lean_ctor_get(v_cfg_2280_, 4);
v_weakLeancArgs_2287_ = lean_ctor_get(v_cfg_2280_, 5);
v_moreLinkObjs_2288_ = lean_ctor_get(v_cfg_2280_, 6);
v_moreLinkLibs_2289_ = lean_ctor_get(v_cfg_2280_, 7);
v_moreLinkArgs_2290_ = lean_ctor_get(v_cfg_2280_, 8);
v_weakLinkArgs_2291_ = lean_ctor_get(v_cfg_2280_, 9);
v_backend_2292_ = lean_ctor_get_uint8(v_cfg_2280_, sizeof(void*)*13 + 1);
v_platformIndependent_2293_ = lean_ctor_get(v_cfg_2280_, 10);
v_precompileImports_2294_ = lean_ctor_get_uint8(v_cfg_2280_, sizeof(void*)*13 + 2);
v_dynlibs_2295_ = lean_ctor_get(v_cfg_2280_, 11);
v_plugins_2296_ = lean_ctor_get(v_cfg_2280_, 12);
v_requiresModuleSystem_2297_ = lean_ctor_get_uint8(v_cfg_2280_, sizeof(void*)*13 + 3);
v_allowNonModules_2298_ = lean_ctor_get_uint8(v_cfg_2280_, sizeof(void*)*13 + 4);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_cfg_2280_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2300_ = v_cfg_2280_;
v_isShared_2301_ = v_isSharedCheck_2308_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_plugins_2296_);
lean_inc(v_dynlibs_2295_);
lean_inc(v_platformIndependent_2293_);
lean_inc(v_weakLinkArgs_2291_);
lean_inc(v_moreLinkArgs_2290_);
lean_inc(v_moreLinkLibs_2289_);
lean_inc(v_moreLinkObjs_2288_);
lean_inc(v_weakLeancArgs_2287_);
lean_inc(v_moreServerOptions_2286_);
lean_inc(v_moreLeancArgs_2285_);
lean_inc(v_weakLeanArgs_2284_);
lean_inc(v_moreLeanArgs_2283_);
lean_inc(v_leanOptions_2282_);
lean_dec(v_cfg_2280_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2308_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2302_ = lean_box(v_requiresModuleSystem_2297_);
v___x_2303_ = lean_apply_1(v_f_2279_, v___x_2302_);
if (v_isShared_2301_ == 0)
{
v___x_2305_ = v___x_2300_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_leanOptions_2282_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_moreLeanArgs_2283_);
lean_ctor_set(v_reuseFailAlloc_2307_, 2, v_weakLeanArgs_2284_);
lean_ctor_set(v_reuseFailAlloc_2307_, 3, v_moreLeancArgs_2285_);
lean_ctor_set(v_reuseFailAlloc_2307_, 4, v_moreServerOptions_2286_);
lean_ctor_set(v_reuseFailAlloc_2307_, 5, v_weakLeancArgs_2287_);
lean_ctor_set(v_reuseFailAlloc_2307_, 6, v_moreLinkObjs_2288_);
lean_ctor_set(v_reuseFailAlloc_2307_, 7, v_moreLinkLibs_2289_);
lean_ctor_set(v_reuseFailAlloc_2307_, 8, v_moreLinkArgs_2290_);
lean_ctor_set(v_reuseFailAlloc_2307_, 9, v_weakLinkArgs_2291_);
lean_ctor_set(v_reuseFailAlloc_2307_, 10, v_platformIndependent_2293_);
lean_ctor_set(v_reuseFailAlloc_2307_, 11, v_dynlibs_2295_);
lean_ctor_set(v_reuseFailAlloc_2307_, 12, v_plugins_2296_);
lean_ctor_set_uint8(v_reuseFailAlloc_2307_, sizeof(void*)*13, v_buildType_2281_);
lean_ctor_set_uint8(v_reuseFailAlloc_2307_, sizeof(void*)*13 + 1, v_backend_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2307_, sizeof(void*)*13 + 2, v_precompileImports_2294_);
v___x_2305_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_unbox(v___x_2303_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*13 + 3, v___x_2306_);
lean_ctor_set_uint8(v___x_2305_, sizeof(void*)*13 + 4, v_allowNonModules_2298_);
return v___x_2305_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object* v_cfg_2319_){
_start:
{
uint8_t v_allowNonModules_2320_; 
v_allowNonModules_2320_ = lean_ctor_get_uint8(v_cfg_2319_, sizeof(void*)*13 + 4);
return v_allowNonModules_2320_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object* v_cfg_2321_){
_start:
{
uint8_t v_res_2322_; lean_object* v_r_2323_; 
v_res_2322_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2321_);
lean_dec_ref(v_cfg_2321_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t v_val_2324_, lean_object* v_cfg_2325_){
_start:
{
uint8_t v_buildType_2326_; lean_object* v_leanOptions_2327_; lean_object* v_moreLeanArgs_2328_; lean_object* v_weakLeanArgs_2329_; lean_object* v_moreLeancArgs_2330_; lean_object* v_moreServerOptions_2331_; lean_object* v_weakLeancArgs_2332_; lean_object* v_moreLinkObjs_2333_; lean_object* v_moreLinkLibs_2334_; lean_object* v_moreLinkArgs_2335_; lean_object* v_weakLinkArgs_2336_; uint8_t v_backend_2337_; lean_object* v_platformIndependent_2338_; uint8_t v_precompileImports_2339_; lean_object* v_dynlibs_2340_; lean_object* v_plugins_2341_; uint8_t v_requiresModuleSystem_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_buildType_2326_ = lean_ctor_get_uint8(v_cfg_2325_, sizeof(void*)*13);
v_leanOptions_2327_ = lean_ctor_get(v_cfg_2325_, 0);
v_moreLeanArgs_2328_ = lean_ctor_get(v_cfg_2325_, 1);
v_weakLeanArgs_2329_ = lean_ctor_get(v_cfg_2325_, 2);
v_moreLeancArgs_2330_ = lean_ctor_get(v_cfg_2325_, 3);
v_moreServerOptions_2331_ = lean_ctor_get(v_cfg_2325_, 4);
v_weakLeancArgs_2332_ = lean_ctor_get(v_cfg_2325_, 5);
v_moreLinkObjs_2333_ = lean_ctor_get(v_cfg_2325_, 6);
v_moreLinkLibs_2334_ = lean_ctor_get(v_cfg_2325_, 7);
v_moreLinkArgs_2335_ = lean_ctor_get(v_cfg_2325_, 8);
v_weakLinkArgs_2336_ = lean_ctor_get(v_cfg_2325_, 9);
v_backend_2337_ = lean_ctor_get_uint8(v_cfg_2325_, sizeof(void*)*13 + 1);
v_platformIndependent_2338_ = lean_ctor_get(v_cfg_2325_, 10);
v_precompileImports_2339_ = lean_ctor_get_uint8(v_cfg_2325_, sizeof(void*)*13 + 2);
v_dynlibs_2340_ = lean_ctor_get(v_cfg_2325_, 11);
v_plugins_2341_ = lean_ctor_get(v_cfg_2325_, 12);
v_requiresModuleSystem_2342_ = lean_ctor_get_uint8(v_cfg_2325_, sizeof(void*)*13 + 3);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_cfg_2325_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v_cfg_2325_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_plugins_2341_);
lean_inc(v_dynlibs_2340_);
lean_inc(v_platformIndependent_2338_);
lean_inc(v_weakLinkArgs_2336_);
lean_inc(v_moreLinkArgs_2335_);
lean_inc(v_moreLinkLibs_2334_);
lean_inc(v_moreLinkObjs_2333_);
lean_inc(v_weakLeancArgs_2332_);
lean_inc(v_moreServerOptions_2331_);
lean_inc(v_moreLeancArgs_2330_);
lean_inc(v_weakLeanArgs_2329_);
lean_inc(v_moreLeanArgs_2328_);
lean_inc(v_leanOptions_2327_);
lean_dec(v_cfg_2325_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_leanOptions_2327_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_moreLeanArgs_2328_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_weakLeanArgs_2329_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_moreLeancArgs_2330_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v_moreServerOptions_2331_);
lean_ctor_set(v_reuseFailAlloc_2348_, 5, v_weakLeancArgs_2332_);
lean_ctor_set(v_reuseFailAlloc_2348_, 6, v_moreLinkObjs_2333_);
lean_ctor_set(v_reuseFailAlloc_2348_, 7, v_moreLinkLibs_2334_);
lean_ctor_set(v_reuseFailAlloc_2348_, 8, v_moreLinkArgs_2335_);
lean_ctor_set(v_reuseFailAlloc_2348_, 9, v_weakLinkArgs_2336_);
lean_ctor_set(v_reuseFailAlloc_2348_, 10, v_platformIndependent_2338_);
lean_ctor_set(v_reuseFailAlloc_2348_, 11, v_dynlibs_2340_);
lean_ctor_set(v_reuseFailAlloc_2348_, 12, v_plugins_2341_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*13, v_buildType_2326_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*13 + 1, v_backend_2337_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*13 + 2, v_precompileImports_2339_);
lean_ctor_set_uint8(v_reuseFailAlloc_2348_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_ctor_set_uint8(v___x_2347_, sizeof(void*)*13 + 4, v_val_2324_);
return v___x_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object* v_val_2350_, lean_object* v_cfg_2351_){
_start:
{
uint8_t v_val_88__boxed_2352_; lean_object* v_res_2353_; 
v_val_88__boxed_2352_ = lean_unbox(v_val_2350_);
v_res_2353_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_88__boxed_2352_, v_cfg_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object* v_f_2354_, lean_object* v_cfg_2355_){
_start:
{
uint8_t v_buildType_2356_; lean_object* v_leanOptions_2357_; lean_object* v_moreLeanArgs_2358_; lean_object* v_weakLeanArgs_2359_; lean_object* v_moreLeancArgs_2360_; lean_object* v_moreServerOptions_2361_; lean_object* v_weakLeancArgs_2362_; lean_object* v_moreLinkObjs_2363_; lean_object* v_moreLinkLibs_2364_; lean_object* v_moreLinkArgs_2365_; lean_object* v_weakLinkArgs_2366_; uint8_t v_backend_2367_; lean_object* v_platformIndependent_2368_; uint8_t v_precompileImports_2369_; lean_object* v_dynlibs_2370_; lean_object* v_plugins_2371_; uint8_t v_requiresModuleSystem_2372_; uint8_t v_allowNonModules_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2383_; 
v_buildType_2356_ = lean_ctor_get_uint8(v_cfg_2355_, sizeof(void*)*13);
v_leanOptions_2357_ = lean_ctor_get(v_cfg_2355_, 0);
v_moreLeanArgs_2358_ = lean_ctor_get(v_cfg_2355_, 1);
v_weakLeanArgs_2359_ = lean_ctor_get(v_cfg_2355_, 2);
v_moreLeancArgs_2360_ = lean_ctor_get(v_cfg_2355_, 3);
v_moreServerOptions_2361_ = lean_ctor_get(v_cfg_2355_, 4);
v_weakLeancArgs_2362_ = lean_ctor_get(v_cfg_2355_, 5);
v_moreLinkObjs_2363_ = lean_ctor_get(v_cfg_2355_, 6);
v_moreLinkLibs_2364_ = lean_ctor_get(v_cfg_2355_, 7);
v_moreLinkArgs_2365_ = lean_ctor_get(v_cfg_2355_, 8);
v_weakLinkArgs_2366_ = lean_ctor_get(v_cfg_2355_, 9);
v_backend_2367_ = lean_ctor_get_uint8(v_cfg_2355_, sizeof(void*)*13 + 1);
v_platformIndependent_2368_ = lean_ctor_get(v_cfg_2355_, 10);
v_precompileImports_2369_ = lean_ctor_get_uint8(v_cfg_2355_, sizeof(void*)*13 + 2);
v_dynlibs_2370_ = lean_ctor_get(v_cfg_2355_, 11);
v_plugins_2371_ = lean_ctor_get(v_cfg_2355_, 12);
v_requiresModuleSystem_2372_ = lean_ctor_get_uint8(v_cfg_2355_, sizeof(void*)*13 + 3);
v_allowNonModules_2373_ = lean_ctor_get_uint8(v_cfg_2355_, sizeof(void*)*13 + 4);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_cfg_2355_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2375_ = v_cfg_2355_;
v_isShared_2376_ = v_isSharedCheck_2383_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_plugins_2371_);
lean_inc(v_dynlibs_2370_);
lean_inc(v_platformIndependent_2368_);
lean_inc(v_weakLinkArgs_2366_);
lean_inc(v_moreLinkArgs_2365_);
lean_inc(v_moreLinkLibs_2364_);
lean_inc(v_moreLinkObjs_2363_);
lean_inc(v_weakLeancArgs_2362_);
lean_inc(v_moreServerOptions_2361_);
lean_inc(v_moreLeancArgs_2360_);
lean_inc(v_weakLeanArgs_2359_);
lean_inc(v_moreLeanArgs_2358_);
lean_inc(v_leanOptions_2357_);
lean_dec(v_cfg_2355_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2383_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2380_; 
v___x_2377_ = lean_box(v_allowNonModules_2373_);
v___x_2378_ = lean_apply_1(v_f_2354_, v___x_2377_);
if (v_isShared_2376_ == 0)
{
v___x_2380_ = v___x_2375_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_leanOptions_2357_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v_moreLeanArgs_2358_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_weakLeanArgs_2359_);
lean_ctor_set(v_reuseFailAlloc_2382_, 3, v_moreLeancArgs_2360_);
lean_ctor_set(v_reuseFailAlloc_2382_, 4, v_moreServerOptions_2361_);
lean_ctor_set(v_reuseFailAlloc_2382_, 5, v_weakLeancArgs_2362_);
lean_ctor_set(v_reuseFailAlloc_2382_, 6, v_moreLinkObjs_2363_);
lean_ctor_set(v_reuseFailAlloc_2382_, 7, v_moreLinkLibs_2364_);
lean_ctor_set(v_reuseFailAlloc_2382_, 8, v_moreLinkArgs_2365_);
lean_ctor_set(v_reuseFailAlloc_2382_, 9, v_weakLinkArgs_2366_);
lean_ctor_set(v_reuseFailAlloc_2382_, 10, v_platformIndependent_2368_);
lean_ctor_set(v_reuseFailAlloc_2382_, 11, v_dynlibs_2370_);
lean_ctor_set(v_reuseFailAlloc_2382_, 12, v_plugins_2371_);
lean_ctor_set_uint8(v_reuseFailAlloc_2382_, sizeof(void*)*13, v_buildType_2356_);
lean_ctor_set_uint8(v_reuseFailAlloc_2382_, sizeof(void*)*13 + 1, v_backend_2367_);
lean_ctor_set_uint8(v_reuseFailAlloc_2382_, sizeof(void*)*13 + 2, v_precompileImports_2369_);
lean_ctor_set_uint8(v_reuseFailAlloc_2382_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2372_);
v___x_2380_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
uint8_t v___x_2381_; 
v___x_2381_ = lean_unbox(v___x_2378_);
lean_ctor_set_uint8(v___x_2380_, sizeof(void*)*13 + 4, v___x_2381_);
return v___x_2380_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2402_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2403_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2404_ = lean_array_push(v___x_2403_, v___x_2402_);
return v___x_2404_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2412_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2413_ = lean_array_push(v___x_2412_, v___x_2411_);
return v___x_2413_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2421_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2422_ = lean_array_push(v___x_2421_, v___x_2420_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2430_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2431_ = lean_array_push(v___x_2430_, v___x_2429_);
return v___x_2431_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2438_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2439_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2440_ = lean_array_push(v___x_2439_, v___x_2438_);
return v___x_2440_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2448_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2449_ = lean_array_push(v___x_2448_, v___x_2447_);
return v___x_2449_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2457_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2458_ = lean_array_push(v___x_2457_, v___x_2456_);
return v___x_2458_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2466_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2467_ = lean_array_push(v___x_2466_, v___x_2465_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2475_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2476_ = lean_array_push(v___x_2475_, v___x_2474_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2483_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2484_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2485_ = lean_array_push(v___x_2484_, v___x_2483_);
return v___x_2485_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2493_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2494_ = lean_array_push(v___x_2493_, v___x_2492_);
return v___x_2494_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2501_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2502_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2503_ = lean_array_push(v___x_2502_, v___x_2501_);
return v___x_2503_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2511_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2512_ = lean_array_push(v___x_2511_, v___x_2510_);
return v___x_2512_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2520_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2521_ = lean_array_push(v___x_2520_, v___x_2519_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2529_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2530_ = lean_array_push(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2537_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__47));
v___x_2538_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
v___x_2539_ = lean_array_push(v___x_2538_, v___x_2537_);
return v___x_2539_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__51(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__50));
v___x_2547_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__48, &l_Lake_LeanConfig___fields___closed__48_once, _init_l_Lake_LeanConfig___fields___closed__48);
v___x_2548_ = lean_array_push(v___x_2547_, v___x_2546_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__54(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__53));
v___x_2556_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__51, &l_Lake_LeanConfig___fields___closed__51_once, _init_l_Lake_LeanConfig___fields___closed__51);
v___x_2557_ = lean_array_push(v___x_2556_, v___x_2555_);
return v___x_2557_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__54, &l_Lake_LeanConfig___fields___closed__54_once, _init_l_Lake_LeanConfig___fields___closed__54);
return v___x_2558_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lake_LeanConfig___fields;
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2560_, lean_object* v_x2_2561_){
_start:
{
lean_object* v_name_2562_; lean_object* v___x_2563_; 
v_name_2562_ = lean_ctor_get(v_x2_2561_, 0);
lean_inc(v_name_2562_);
v___x_2563_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2562_, v_x2_2561_, v_x1_2560_);
return v___x_2563_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = l_Lake_LeanConfig___fields;
v___x_2565_ = lean_array_get_size(v___x_2564_);
return v___x_2565_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2585_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = lean_nat_dec_lt(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2588_ = lean_unsigned_to_nat(0u);
v___x_2589_ = lean_box(1);
v___x_2590_ = l_Lake_LeanConfig___fields;
v___x_2591_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v___x_2589_);
lean_ctor_set(v___x_2591_, 2, v___x_2588_);
return v___x_2591_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2594_ = lean_nat_dec_le(v___x_2593_, v___x_2593_);
return v___x_2594_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2595_; size_t v___x_2596_; 
v___x_2595_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2596_ = lean_usize_of_nat(v___x_2595_);
return v___x_2596_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2597_; size_t v___x_2598_; size_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___f_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2597_ = lean_box(1);
v___x_2598_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = l_Lake_LeanConfig___fields;
v___f_2601_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2602_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2602_, v___f_2601_, v___x_2600_, v___x_2599_, v___x_2598_, v___x_2597_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2606_ = l_Lake_LeanConfig___fields;
v___x_2607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
lean_ctor_set(v___x_2607_, 1, v___x_2605_);
lean_ctor_set(v___x_2607_, 2, v___x_2604_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; 
v___x_2609_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2609_;
}
else
{
uint8_t v___x_2610_; 
v___x_2610_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2610_ == 0)
{
if (v___x_2608_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2611_;
}
else
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2612_;
}
}
else
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2613_;
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

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
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = lean_unsigned_to_nat(24u);
v___x_856_ = lean_nat_to_int(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(19u);
v___x_861_ = lean_nat_to_int(v___x_860_);
return v___x_861_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_864_ = lean_string_length(v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52(void){
_start:
{
lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_865_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__51, &l_Lake_instReprLeanConfig_repr___redArg___closed__51_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__51);
v___x_866_ = lean_nat_to_int(v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_871_){
_start:
{
uint8_t v_buildType_872_; lean_object* v_leanOptions_873_; lean_object* v_moreLeanArgs_874_; lean_object* v_weakLeanArgs_875_; lean_object* v_moreLeancArgs_876_; lean_object* v_moreServerOptions_877_; lean_object* v_weakLeancArgs_878_; lean_object* v_moreLinkObjs_879_; lean_object* v_moreLinkLibs_880_; lean_object* v_moreLinkArgs_881_; lean_object* v_weakLinkArgs_882_; uint8_t v_backend_883_; lean_object* v_platformIndependent_884_; uint8_t v_precompileImports_885_; lean_object* v_dynlibs_886_; lean_object* v_plugins_887_; uint8_t v_requiresModuleSystem_888_; uint8_t v_allowNonModules_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_buildType_872_ = lean_ctor_get_uint8(v_x_871_, sizeof(void*)*13);
v_leanOptions_873_ = lean_ctor_get(v_x_871_, 0);
lean_inc_ref(v_leanOptions_873_);
v_moreLeanArgs_874_ = lean_ctor_get(v_x_871_, 1);
lean_inc_ref(v_moreLeanArgs_874_);
v_weakLeanArgs_875_ = lean_ctor_get(v_x_871_, 2);
lean_inc_ref(v_weakLeanArgs_875_);
v_moreLeancArgs_876_ = lean_ctor_get(v_x_871_, 3);
lean_inc_ref(v_moreLeancArgs_876_);
v_moreServerOptions_877_ = lean_ctor_get(v_x_871_, 4);
lean_inc_ref(v_moreServerOptions_877_);
v_weakLeancArgs_878_ = lean_ctor_get(v_x_871_, 5);
lean_inc_ref(v_weakLeancArgs_878_);
v_moreLinkObjs_879_ = lean_ctor_get(v_x_871_, 6);
lean_inc_ref(v_moreLinkObjs_879_);
v_moreLinkLibs_880_ = lean_ctor_get(v_x_871_, 7);
lean_inc_ref(v_moreLinkLibs_880_);
v_moreLinkArgs_881_ = lean_ctor_get(v_x_871_, 8);
lean_inc_ref(v_moreLinkArgs_881_);
v_weakLinkArgs_882_ = lean_ctor_get(v_x_871_, 9);
lean_inc_ref(v_weakLinkArgs_882_);
v_backend_883_ = lean_ctor_get_uint8(v_x_871_, sizeof(void*)*13 + 1);
v_platformIndependent_884_ = lean_ctor_get(v_x_871_, 10);
lean_inc(v_platformIndependent_884_);
v_precompileImports_885_ = lean_ctor_get_uint8(v_x_871_, sizeof(void*)*13 + 2);
v_dynlibs_886_ = lean_ctor_get(v_x_871_, 11);
lean_inc_ref(v_dynlibs_886_);
v_plugins_887_ = lean_ctor_get(v_x_871_, 12);
lean_inc_ref(v_plugins_887_);
v_requiresModuleSystem_888_ = lean_ctor_get_uint8(v_x_871_, sizeof(void*)*13 + 3);
v_allowNonModules_889_ = lean_ctor_get_uint8(v_x_871_, sizeof(void*)*13 + 4);
lean_dec_ref(v_x_871_);
v___x_890_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_891_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_892_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = l_Lake_instReprBuildType_repr(v_buildType_872_, v___x_893_);
v___x_895_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_892_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = 0;
v___x_897_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set_uint8(v___x_897_, sizeof(void*)*1, v___x_896_);
v___x_898_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_891_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2));
v___x_900_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_box(1);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_900_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__9));
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_890_);
v___x_906_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__10, &l_Lake_instReprLeanConfig_repr___redArg___closed__10_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10);
v___x_907_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_873_);
v___x_908_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set_uint8(v___x_909_, sizeof(void*)*1, v___x_896_);
v___x_910_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_905_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_899_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v___x_901_);
v___x_913_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__12));
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_912_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_890_);
v___x_916_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__13, &l_Lake_instReprLeanConfig_repr___redArg___closed__13_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13);
v___x_917_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_874_);
v___x_918_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*1, v___x_896_);
v___x_920_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_915_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v___x_899_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_901_);
v___x_923_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__15));
v___x_924_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
lean_ctor_set(v___x_925_, 1, v___x_890_);
v___x_926_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_875_);
v___x_927_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_916_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set_uint8(v___x_928_, sizeof(void*)*1, v___x_896_);
v___x_929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_925_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set(v___x_930_, 1, v___x_899_);
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
lean_ctor_set(v___x_931_, 1, v___x_901_);
v___x_932_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__17));
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_890_);
v___x_935_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__18, &l_Lake_instReprLeanConfig_repr___redArg___closed__18_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18);
v___x_936_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_876_);
v___x_937_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set_uint8(v___x_938_, sizeof(void*)*1, v___x_896_);
v___x_939_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_934_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set(v___x_940_, 1, v___x_899_);
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_901_);
v___x_942_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__20));
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_890_);
v___x_945_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__21, &l_Lake_instReprLeanConfig_repr___redArg___closed__21_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21);
v___x_946_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_877_);
v___x_947_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_947_, 0, v___x_945_);
lean_ctor_set(v___x_947_, 1, v___x_946_);
v___x_948_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_948_, 0, v___x_947_);
lean_ctor_set_uint8(v___x_948_, sizeof(void*)*1, v___x_896_);
v___x_949_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_944_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_949_);
lean_ctor_set(v___x_950_, 1, v___x_899_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_901_);
v___x_952_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__23));
v___x_953_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_890_);
v___x_955_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_878_);
v___x_956_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_935_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
v___x_957_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set_uint8(v___x_957_, sizeof(void*)*1, v___x_896_);
v___x_958_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_954_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_899_);
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_901_);
v___x_961_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__25));
v___x_962_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v___x_890_);
v___x_964_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_879_);
v___x_965_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_916_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set_uint8(v___x_966_, sizeof(void*)*1, v___x_896_);
v___x_967_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_963_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_899_);
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_901_);
v___x_970_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__27));
v___x_971_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_890_);
v___x_973_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_880_);
v___x_974_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_916_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_975_, 0, v___x_974_);
lean_ctor_set_uint8(v___x_975_, sizeof(void*)*1, v___x_896_);
v___x_976_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_972_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
lean_ctor_set(v___x_977_, 1, v___x_899_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_901_);
v___x_979_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__29));
v___x_980_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_890_);
v___x_982_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_881_);
v___x_983_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_916_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*1, v___x_896_);
v___x_985_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_981_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_899_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_901_);
v___x_988_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__31));
v___x_989_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_987_);
lean_ctor_set(v___x_989_, 1, v___x_988_);
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
lean_ctor_set(v___x_990_, 1, v___x_890_);
v___x_991_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_882_);
v___x_992_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_916_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*1, v___x_896_);
v___x_994_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_990_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_899_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v___x_901_);
v___x_997_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__33));
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_890_);
v___x_1000_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__34, &l_Lake_instReprLeanConfig_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34);
v___x_1001_ = l_Lake_instReprBackend_repr(v_backend_883_, v___x_893_);
v___x_1002_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1003_, 0, v___x_1002_);
lean_ctor_set_uint8(v___x_1003_, sizeof(void*)*1, v___x_896_);
v___x_1004_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_999_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v___x_899_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_901_);
v___x_1007_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__36));
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1006_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
lean_ctor_set(v___x_1009_, 1, v___x_890_);
v___x_1010_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__37, &l_Lake_instReprLeanConfig_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37);
v___x_1011_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_884_, v___x_893_);
lean_dec(v_platformIndependent_884_);
v___x_1012_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set_uint8(v___x_1013_, sizeof(void*)*1, v___x_896_);
v___x_1014_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1009_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
lean_ctor_set(v___x_1015_, 1, v___x_899_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_901_);
v___x_1017_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__39));
v___x_1018_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1016_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v___x_890_);
v___x_1020_ = l_Bool_repr___redArg(v_precompileImports_885_);
v___x_1021_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_945_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
lean_ctor_set_uint8(v___x_1022_, sizeof(void*)*1, v___x_896_);
v___x_1023_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1019_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v___x_899_);
v___x_1025_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_901_);
v___x_1026_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__41));
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v___x_890_);
v___x_1029_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_886_);
v___x_1030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1000_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*1, v___x_896_);
v___x_1032_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1028_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
lean_ctor_set(v___x_1033_, 1, v___x_899_);
v___x_1034_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_901_);
v___x_1035_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__43));
v___x_1036_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_890_);
v___x_1038_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_887_);
v___x_1039_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1000_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set_uint8(v___x_1040_, sizeof(void*)*1, v___x_896_);
v___x_1041_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1037_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___x_899_);
v___x_1043_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___x_901_);
v___x_1044_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__45));
v___x_1045_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_890_);
v___x_1047_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__46, &l_Lake_instReprLeanConfig_repr___redArg___closed__46_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__46);
v___x_1048_ = l_Bool_repr___redArg(v_requiresModuleSystem_888_);
v___x_1049_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*1, v___x_896_);
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1046_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_899_);
v___x_1053_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1052_);
lean_ctor_set(v___x_1053_, 1, v___x_901_);
v___x_1054_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__48));
v___x_1055_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set(v___x_1056_, 1, v___x_890_);
v___x_1057_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__49, &l_Lake_instReprLeanConfig_repr___redArg___closed__49_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49);
v___x_1058_ = l_Bool_repr___redArg(v_allowNonModules_889_);
v___x_1059_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set_uint8(v___x_1060_, sizeof(void*)*1, v___x_896_);
v___x_1061_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1056_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1062_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__52, &l_Lake_instReprLeanConfig_repr___redArg___closed__52_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__52);
v___x_1063_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__53));
v___x_1064_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___x_1061_);
v___x_1065_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__54));
v___x_1066_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1062_);
lean_ctor_set(v___x_1067_, 1, v___x_1066_);
v___x_1068_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*1, v___x_896_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1069_, lean_object* v_prec_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1072_, lean_object* v_prec_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lake_instReprLeanConfig_repr(v_x_1072_, v_prec_1073_);
lean_dec(v_prec_1073_);
return v_res_1074_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1077_){
_start:
{
uint8_t v_buildType_1078_; 
v_buildType_1078_ = lean_ctor_get_uint8(v_cfg_1077_, sizeof(void*)*13);
return v_buildType_1078_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1079_){
_start:
{
uint8_t v_res_1080_; lean_object* v_r_1081_; 
v_res_1080_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1079_);
lean_dec_ref(v_cfg_1079_);
v_r_1081_ = lean_box(v_res_1080_);
return v_r_1081_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1082_, lean_object* v_cfg_1083_){
_start:
{
lean_object* v_leanOptions_1084_; lean_object* v_moreLeanArgs_1085_; lean_object* v_weakLeanArgs_1086_; lean_object* v_moreLeancArgs_1087_; lean_object* v_moreServerOptions_1088_; lean_object* v_weakLeancArgs_1089_; lean_object* v_moreLinkObjs_1090_; lean_object* v_moreLinkLibs_1091_; lean_object* v_moreLinkArgs_1092_; lean_object* v_weakLinkArgs_1093_; uint8_t v_backend_1094_; lean_object* v_platformIndependent_1095_; uint8_t v_precompileImports_1096_; lean_object* v_dynlibs_1097_; lean_object* v_plugins_1098_; uint8_t v_requiresModuleSystem_1099_; uint8_t v_allowNonModules_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_leanOptions_1084_ = lean_ctor_get(v_cfg_1083_, 0);
v_moreLeanArgs_1085_ = lean_ctor_get(v_cfg_1083_, 1);
v_weakLeanArgs_1086_ = lean_ctor_get(v_cfg_1083_, 2);
v_moreLeancArgs_1087_ = lean_ctor_get(v_cfg_1083_, 3);
v_moreServerOptions_1088_ = lean_ctor_get(v_cfg_1083_, 4);
v_weakLeancArgs_1089_ = lean_ctor_get(v_cfg_1083_, 5);
v_moreLinkObjs_1090_ = lean_ctor_get(v_cfg_1083_, 6);
v_moreLinkLibs_1091_ = lean_ctor_get(v_cfg_1083_, 7);
v_moreLinkArgs_1092_ = lean_ctor_get(v_cfg_1083_, 8);
v_weakLinkArgs_1093_ = lean_ctor_get(v_cfg_1083_, 9);
v_backend_1094_ = lean_ctor_get_uint8(v_cfg_1083_, sizeof(void*)*13 + 1);
v_platformIndependent_1095_ = lean_ctor_get(v_cfg_1083_, 10);
v_precompileImports_1096_ = lean_ctor_get_uint8(v_cfg_1083_, sizeof(void*)*13 + 2);
v_dynlibs_1097_ = lean_ctor_get(v_cfg_1083_, 11);
v_plugins_1098_ = lean_ctor_get(v_cfg_1083_, 12);
v_requiresModuleSystem_1099_ = lean_ctor_get_uint8(v_cfg_1083_, sizeof(void*)*13 + 3);
v_allowNonModules_1100_ = lean_ctor_get_uint8(v_cfg_1083_, sizeof(void*)*13 + 4);
v_isSharedCheck_1107_ = !lean_is_exclusive(v_cfg_1083_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v_cfg_1083_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_plugins_1098_);
lean_inc(v_dynlibs_1097_);
lean_inc(v_platformIndependent_1095_);
lean_inc(v_weakLinkArgs_1093_);
lean_inc(v_moreLinkArgs_1092_);
lean_inc(v_moreLinkLibs_1091_);
lean_inc(v_moreLinkObjs_1090_);
lean_inc(v_weakLeancArgs_1089_);
lean_inc(v_moreServerOptions_1088_);
lean_inc(v_moreLeancArgs_1087_);
lean_inc(v_weakLeanArgs_1086_);
lean_inc(v_moreLeanArgs_1085_);
lean_inc(v_leanOptions_1084_);
lean_dec(v_cfg_1083_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_leanOptions_1084_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_moreLeanArgs_1085_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_weakLeanArgs_1086_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v_moreLeancArgs_1087_);
lean_ctor_set(v_reuseFailAlloc_1106_, 4, v_moreServerOptions_1088_);
lean_ctor_set(v_reuseFailAlloc_1106_, 5, v_weakLeancArgs_1089_);
lean_ctor_set(v_reuseFailAlloc_1106_, 6, v_moreLinkObjs_1090_);
lean_ctor_set(v_reuseFailAlloc_1106_, 7, v_moreLinkLibs_1091_);
lean_ctor_set(v_reuseFailAlloc_1106_, 8, v_moreLinkArgs_1092_);
lean_ctor_set(v_reuseFailAlloc_1106_, 9, v_weakLinkArgs_1093_);
lean_ctor_set(v_reuseFailAlloc_1106_, 10, v_platformIndependent_1095_);
lean_ctor_set(v_reuseFailAlloc_1106_, 11, v_dynlibs_1097_);
lean_ctor_set(v_reuseFailAlloc_1106_, 12, v_plugins_1098_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*13 + 1, v_backend_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*13 + 2, v_precompileImports_1096_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1099_);
lean_ctor_set_uint8(v_reuseFailAlloc_1106_, sizeof(void*)*13 + 4, v_allowNonModules_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_ctor_set_uint8(v___x_1105_, sizeof(void*)*13, v_val_1082_);
return v___x_1105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1108_, lean_object* v_cfg_1109_){
_start:
{
uint8_t v_val_88__boxed_1110_; lean_object* v_res_1111_; 
v_val_88__boxed_1110_ = lean_unbox(v_val_1108_);
v_res_1111_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_88__boxed_1110_, v_cfg_1109_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1112_, lean_object* v_cfg_1113_){
_start:
{
uint8_t v_buildType_1114_; lean_object* v_leanOptions_1115_; lean_object* v_moreLeanArgs_1116_; lean_object* v_weakLeanArgs_1117_; lean_object* v_moreLeancArgs_1118_; lean_object* v_moreServerOptions_1119_; lean_object* v_weakLeancArgs_1120_; lean_object* v_moreLinkObjs_1121_; lean_object* v_moreLinkLibs_1122_; lean_object* v_moreLinkArgs_1123_; lean_object* v_weakLinkArgs_1124_; uint8_t v_backend_1125_; lean_object* v_platformIndependent_1126_; uint8_t v_precompileImports_1127_; lean_object* v_dynlibs_1128_; lean_object* v_plugins_1129_; uint8_t v_requiresModuleSystem_1130_; uint8_t v_allowNonModules_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1141_; 
v_buildType_1114_ = lean_ctor_get_uint8(v_cfg_1113_, sizeof(void*)*13);
v_leanOptions_1115_ = lean_ctor_get(v_cfg_1113_, 0);
v_moreLeanArgs_1116_ = lean_ctor_get(v_cfg_1113_, 1);
v_weakLeanArgs_1117_ = lean_ctor_get(v_cfg_1113_, 2);
v_moreLeancArgs_1118_ = lean_ctor_get(v_cfg_1113_, 3);
v_moreServerOptions_1119_ = lean_ctor_get(v_cfg_1113_, 4);
v_weakLeancArgs_1120_ = lean_ctor_get(v_cfg_1113_, 5);
v_moreLinkObjs_1121_ = lean_ctor_get(v_cfg_1113_, 6);
v_moreLinkLibs_1122_ = lean_ctor_get(v_cfg_1113_, 7);
v_moreLinkArgs_1123_ = lean_ctor_get(v_cfg_1113_, 8);
v_weakLinkArgs_1124_ = lean_ctor_get(v_cfg_1113_, 9);
v_backend_1125_ = lean_ctor_get_uint8(v_cfg_1113_, sizeof(void*)*13 + 1);
v_platformIndependent_1126_ = lean_ctor_get(v_cfg_1113_, 10);
v_precompileImports_1127_ = lean_ctor_get_uint8(v_cfg_1113_, sizeof(void*)*13 + 2);
v_dynlibs_1128_ = lean_ctor_get(v_cfg_1113_, 11);
v_plugins_1129_ = lean_ctor_get(v_cfg_1113_, 12);
v_requiresModuleSystem_1130_ = lean_ctor_get_uint8(v_cfg_1113_, sizeof(void*)*13 + 3);
v_allowNonModules_1131_ = lean_ctor_get_uint8(v_cfg_1113_, sizeof(void*)*13 + 4);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_cfg_1113_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1133_ = v_cfg_1113_;
v_isShared_1134_ = v_isSharedCheck_1141_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_plugins_1129_);
lean_inc(v_dynlibs_1128_);
lean_inc(v_platformIndependent_1126_);
lean_inc(v_weakLinkArgs_1124_);
lean_inc(v_moreLinkArgs_1123_);
lean_inc(v_moreLinkLibs_1122_);
lean_inc(v_moreLinkObjs_1121_);
lean_inc(v_weakLeancArgs_1120_);
lean_inc(v_moreServerOptions_1119_);
lean_inc(v_moreLeancArgs_1118_);
lean_inc(v_weakLeanArgs_1117_);
lean_inc(v_moreLeanArgs_1116_);
lean_inc(v_leanOptions_1115_);
lean_dec(v_cfg_1113_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1141_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1135_ = lean_box(v_buildType_1114_);
v___x_1136_ = lean_apply_1(v_f_1112_, v___x_1135_);
if (v_isShared_1134_ == 0)
{
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_leanOptions_1115_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_moreLeanArgs_1116_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_weakLeanArgs_1117_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_moreLeancArgs_1118_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_moreServerOptions_1119_);
lean_ctor_set(v_reuseFailAlloc_1140_, 5, v_weakLeancArgs_1120_);
lean_ctor_set(v_reuseFailAlloc_1140_, 6, v_moreLinkObjs_1121_);
lean_ctor_set(v_reuseFailAlloc_1140_, 7, v_moreLinkLibs_1122_);
lean_ctor_set(v_reuseFailAlloc_1140_, 8, v_moreLinkArgs_1123_);
lean_ctor_set(v_reuseFailAlloc_1140_, 9, v_weakLinkArgs_1124_);
lean_ctor_set(v_reuseFailAlloc_1140_, 10, v_platformIndependent_1126_);
lean_ctor_set(v_reuseFailAlloc_1140_, 11, v_dynlibs_1128_);
lean_ctor_set(v_reuseFailAlloc_1140_, 12, v_plugins_1129_);
v___x_1138_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_unbox(v___x_1136_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*13, v___x_1139_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*13 + 1, v_backend_1125_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*13 + 2, v_precompileImports_1127_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1130_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*13 + 4, v_allowNonModules_1131_);
return v___x_1138_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1142_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = 3;
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1144_){
_start:
{
uint8_t v_res_1145_; lean_object* v_r_1146_; 
v_res_1145_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1144_);
lean_dec_ref(v_x_1144_);
v_r_1146_ = lean_box(v_res_1145_);
return v_r_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1158_){
_start:
{
lean_object* v_leanOptions_1159_; 
v_leanOptions_1159_ = lean_ctor_get(v_cfg_1158_, 0);
lean_inc_ref(v_leanOptions_1159_);
return v_leanOptions_1159_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1160_);
lean_dec_ref(v_cfg_1160_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1162_, lean_object* v_cfg_1163_){
_start:
{
uint8_t v_buildType_1164_; lean_object* v_moreLeanArgs_1165_; lean_object* v_weakLeanArgs_1166_; lean_object* v_moreLeancArgs_1167_; lean_object* v_moreServerOptions_1168_; lean_object* v_weakLeancArgs_1169_; lean_object* v_moreLinkObjs_1170_; lean_object* v_moreLinkLibs_1171_; lean_object* v_moreLinkArgs_1172_; lean_object* v_weakLinkArgs_1173_; uint8_t v_backend_1174_; lean_object* v_platformIndependent_1175_; uint8_t v_precompileImports_1176_; lean_object* v_dynlibs_1177_; lean_object* v_plugins_1178_; uint8_t v_requiresModuleSystem_1179_; uint8_t v_allowNonModules_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
v_buildType_1164_ = lean_ctor_get_uint8(v_cfg_1163_, sizeof(void*)*13);
v_moreLeanArgs_1165_ = lean_ctor_get(v_cfg_1163_, 1);
v_weakLeanArgs_1166_ = lean_ctor_get(v_cfg_1163_, 2);
v_moreLeancArgs_1167_ = lean_ctor_get(v_cfg_1163_, 3);
v_moreServerOptions_1168_ = lean_ctor_get(v_cfg_1163_, 4);
v_weakLeancArgs_1169_ = lean_ctor_get(v_cfg_1163_, 5);
v_moreLinkObjs_1170_ = lean_ctor_get(v_cfg_1163_, 6);
v_moreLinkLibs_1171_ = lean_ctor_get(v_cfg_1163_, 7);
v_moreLinkArgs_1172_ = lean_ctor_get(v_cfg_1163_, 8);
v_weakLinkArgs_1173_ = lean_ctor_get(v_cfg_1163_, 9);
v_backend_1174_ = lean_ctor_get_uint8(v_cfg_1163_, sizeof(void*)*13 + 1);
v_platformIndependent_1175_ = lean_ctor_get(v_cfg_1163_, 10);
v_precompileImports_1176_ = lean_ctor_get_uint8(v_cfg_1163_, sizeof(void*)*13 + 2);
v_dynlibs_1177_ = lean_ctor_get(v_cfg_1163_, 11);
v_plugins_1178_ = lean_ctor_get(v_cfg_1163_, 12);
v_requiresModuleSystem_1179_ = lean_ctor_get_uint8(v_cfg_1163_, sizeof(void*)*13 + 3);
v_allowNonModules_1180_ = lean_ctor_get_uint8(v_cfg_1163_, sizeof(void*)*13 + 4);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_cfg_1163_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; 
v_unused_1188_ = lean_ctor_get(v_cfg_1163_, 0);
lean_dec(v_unused_1188_);
v___x_1182_ = v_cfg_1163_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_plugins_1178_);
lean_inc(v_dynlibs_1177_);
lean_inc(v_platformIndependent_1175_);
lean_inc(v_weakLinkArgs_1173_);
lean_inc(v_moreLinkArgs_1172_);
lean_inc(v_moreLinkLibs_1171_);
lean_inc(v_moreLinkObjs_1170_);
lean_inc(v_weakLeancArgs_1169_);
lean_inc(v_moreServerOptions_1168_);
lean_inc(v_moreLeancArgs_1167_);
lean_inc(v_weakLeanArgs_1166_);
lean_inc(v_moreLeanArgs_1165_);
lean_dec(v_cfg_1163_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1185_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v_val_1162_);
v___x_1185_ = v___x_1182_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_val_1162_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_moreLeanArgs_1165_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_weakLeanArgs_1166_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_moreLeancArgs_1167_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_moreServerOptions_1168_);
lean_ctor_set(v_reuseFailAlloc_1186_, 5, v_weakLeancArgs_1169_);
lean_ctor_set(v_reuseFailAlloc_1186_, 6, v_moreLinkObjs_1170_);
lean_ctor_set(v_reuseFailAlloc_1186_, 7, v_moreLinkLibs_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 8, v_moreLinkArgs_1172_);
lean_ctor_set(v_reuseFailAlloc_1186_, 9, v_weakLinkArgs_1173_);
lean_ctor_set(v_reuseFailAlloc_1186_, 10, v_platformIndependent_1175_);
lean_ctor_set(v_reuseFailAlloc_1186_, 11, v_dynlibs_1177_);
lean_ctor_set(v_reuseFailAlloc_1186_, 12, v_plugins_1178_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*13, v_buildType_1164_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*13 + 1, v_backend_1174_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*13 + 2, v_precompileImports_1176_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1179_);
lean_ctor_set_uint8(v_reuseFailAlloc_1186_, sizeof(void*)*13 + 4, v_allowNonModules_1180_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1189_, lean_object* v_cfg_1190_){
_start:
{
uint8_t v_buildType_1191_; lean_object* v_leanOptions_1192_; lean_object* v_moreLeanArgs_1193_; lean_object* v_weakLeanArgs_1194_; lean_object* v_moreLeancArgs_1195_; lean_object* v_moreServerOptions_1196_; lean_object* v_weakLeancArgs_1197_; lean_object* v_moreLinkObjs_1198_; lean_object* v_moreLinkLibs_1199_; lean_object* v_moreLinkArgs_1200_; lean_object* v_weakLinkArgs_1201_; uint8_t v_backend_1202_; lean_object* v_platformIndependent_1203_; uint8_t v_precompileImports_1204_; lean_object* v_dynlibs_1205_; lean_object* v_plugins_1206_; uint8_t v_requiresModuleSystem_1207_; uint8_t v_allowNonModules_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1216_; 
v_buildType_1191_ = lean_ctor_get_uint8(v_cfg_1190_, sizeof(void*)*13);
v_leanOptions_1192_ = lean_ctor_get(v_cfg_1190_, 0);
v_moreLeanArgs_1193_ = lean_ctor_get(v_cfg_1190_, 1);
v_weakLeanArgs_1194_ = lean_ctor_get(v_cfg_1190_, 2);
v_moreLeancArgs_1195_ = lean_ctor_get(v_cfg_1190_, 3);
v_moreServerOptions_1196_ = lean_ctor_get(v_cfg_1190_, 4);
v_weakLeancArgs_1197_ = lean_ctor_get(v_cfg_1190_, 5);
v_moreLinkObjs_1198_ = lean_ctor_get(v_cfg_1190_, 6);
v_moreLinkLibs_1199_ = lean_ctor_get(v_cfg_1190_, 7);
v_moreLinkArgs_1200_ = lean_ctor_get(v_cfg_1190_, 8);
v_weakLinkArgs_1201_ = lean_ctor_get(v_cfg_1190_, 9);
v_backend_1202_ = lean_ctor_get_uint8(v_cfg_1190_, sizeof(void*)*13 + 1);
v_platformIndependent_1203_ = lean_ctor_get(v_cfg_1190_, 10);
v_precompileImports_1204_ = lean_ctor_get_uint8(v_cfg_1190_, sizeof(void*)*13 + 2);
v_dynlibs_1205_ = lean_ctor_get(v_cfg_1190_, 11);
v_plugins_1206_ = lean_ctor_get(v_cfg_1190_, 12);
v_requiresModuleSystem_1207_ = lean_ctor_get_uint8(v_cfg_1190_, sizeof(void*)*13 + 3);
v_allowNonModules_1208_ = lean_ctor_get_uint8(v_cfg_1190_, sizeof(void*)*13 + 4);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_cfg_1190_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1210_ = v_cfg_1190_;
v_isShared_1211_ = v_isSharedCheck_1216_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_plugins_1206_);
lean_inc(v_dynlibs_1205_);
lean_inc(v_platformIndependent_1203_);
lean_inc(v_weakLinkArgs_1201_);
lean_inc(v_moreLinkArgs_1200_);
lean_inc(v_moreLinkLibs_1199_);
lean_inc(v_moreLinkObjs_1198_);
lean_inc(v_weakLeancArgs_1197_);
lean_inc(v_moreServerOptions_1196_);
lean_inc(v_moreLeancArgs_1195_);
lean_inc(v_weakLeanArgs_1194_);
lean_inc(v_moreLeanArgs_1193_);
lean_inc(v_leanOptions_1192_);
lean_dec(v_cfg_1190_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1216_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1212_ = lean_apply_1(v_f_1189_, v_leanOptions_1192_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1212_);
v___x_1214_ = v___x_1210_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_moreLeanArgs_1193_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_weakLeanArgs_1194_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_moreLeancArgs_1195_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_moreServerOptions_1196_);
lean_ctor_set(v_reuseFailAlloc_1215_, 5, v_weakLeancArgs_1197_);
lean_ctor_set(v_reuseFailAlloc_1215_, 6, v_moreLinkObjs_1198_);
lean_ctor_set(v_reuseFailAlloc_1215_, 7, v_moreLinkLibs_1199_);
lean_ctor_set(v_reuseFailAlloc_1215_, 8, v_moreLinkArgs_1200_);
lean_ctor_set(v_reuseFailAlloc_1215_, 9, v_weakLinkArgs_1201_);
lean_ctor_set(v_reuseFailAlloc_1215_, 10, v_platformIndependent_1203_);
lean_ctor_set(v_reuseFailAlloc_1215_, 11, v_dynlibs_1205_);
lean_ctor_set(v_reuseFailAlloc_1215_, 12, v_plugins_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*13, v_buildType_1191_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*13 + 1, v_backend_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*13 + 2, v_precompileImports_1204_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1215_, sizeof(void*)*13 + 4, v_allowNonModules_1208_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1219_);
lean_dec_ref(v_x_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1232_){
_start:
{
lean_object* v_moreLeanArgs_1233_; 
v_moreLeanArgs_1233_ = lean_ctor_get(v_cfg_1232_, 1);
lean_inc_ref(v_moreLeanArgs_1233_);
return v_moreLeanArgs_1233_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1234_);
lean_dec_ref(v_cfg_1234_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1236_, lean_object* v_cfg_1237_){
_start:
{
uint8_t v_buildType_1238_; lean_object* v_leanOptions_1239_; lean_object* v_weakLeanArgs_1240_; lean_object* v_moreLeancArgs_1241_; lean_object* v_moreServerOptions_1242_; lean_object* v_weakLeancArgs_1243_; lean_object* v_moreLinkObjs_1244_; lean_object* v_moreLinkLibs_1245_; lean_object* v_moreLinkArgs_1246_; lean_object* v_weakLinkArgs_1247_; uint8_t v_backend_1248_; lean_object* v_platformIndependent_1249_; uint8_t v_precompileImports_1250_; lean_object* v_dynlibs_1251_; lean_object* v_plugins_1252_; uint8_t v_requiresModuleSystem_1253_; uint8_t v_allowNonModules_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_buildType_1238_ = lean_ctor_get_uint8(v_cfg_1237_, sizeof(void*)*13);
v_leanOptions_1239_ = lean_ctor_get(v_cfg_1237_, 0);
v_weakLeanArgs_1240_ = lean_ctor_get(v_cfg_1237_, 2);
v_moreLeancArgs_1241_ = lean_ctor_get(v_cfg_1237_, 3);
v_moreServerOptions_1242_ = lean_ctor_get(v_cfg_1237_, 4);
v_weakLeancArgs_1243_ = lean_ctor_get(v_cfg_1237_, 5);
v_moreLinkObjs_1244_ = lean_ctor_get(v_cfg_1237_, 6);
v_moreLinkLibs_1245_ = lean_ctor_get(v_cfg_1237_, 7);
v_moreLinkArgs_1246_ = lean_ctor_get(v_cfg_1237_, 8);
v_weakLinkArgs_1247_ = lean_ctor_get(v_cfg_1237_, 9);
v_backend_1248_ = lean_ctor_get_uint8(v_cfg_1237_, sizeof(void*)*13 + 1);
v_platformIndependent_1249_ = lean_ctor_get(v_cfg_1237_, 10);
v_precompileImports_1250_ = lean_ctor_get_uint8(v_cfg_1237_, sizeof(void*)*13 + 2);
v_dynlibs_1251_ = lean_ctor_get(v_cfg_1237_, 11);
v_plugins_1252_ = lean_ctor_get(v_cfg_1237_, 12);
v_requiresModuleSystem_1253_ = lean_ctor_get_uint8(v_cfg_1237_, sizeof(void*)*13 + 3);
v_allowNonModules_1254_ = lean_ctor_get_uint8(v_cfg_1237_, sizeof(void*)*13 + 4);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_cfg_1237_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v_cfg_1237_, 1);
lean_dec(v_unused_1262_);
v___x_1256_ = v_cfg_1237_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_plugins_1252_);
lean_inc(v_dynlibs_1251_);
lean_inc(v_platformIndependent_1249_);
lean_inc(v_weakLinkArgs_1247_);
lean_inc(v_moreLinkArgs_1246_);
lean_inc(v_moreLinkLibs_1245_);
lean_inc(v_moreLinkObjs_1244_);
lean_inc(v_weakLeancArgs_1243_);
lean_inc(v_moreServerOptions_1242_);
lean_inc(v_moreLeancArgs_1241_);
lean_inc(v_weakLeanArgs_1240_);
lean_inc(v_leanOptions_1239_);
lean_dec(v_cfg_1237_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_val_1236_);
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_leanOptions_1239_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_val_1236_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_weakLeanArgs_1240_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_moreLeancArgs_1241_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_moreServerOptions_1242_);
lean_ctor_set(v_reuseFailAlloc_1260_, 5, v_weakLeancArgs_1243_);
lean_ctor_set(v_reuseFailAlloc_1260_, 6, v_moreLinkObjs_1244_);
lean_ctor_set(v_reuseFailAlloc_1260_, 7, v_moreLinkLibs_1245_);
lean_ctor_set(v_reuseFailAlloc_1260_, 8, v_moreLinkArgs_1246_);
lean_ctor_set(v_reuseFailAlloc_1260_, 9, v_weakLinkArgs_1247_);
lean_ctor_set(v_reuseFailAlloc_1260_, 10, v_platformIndependent_1249_);
lean_ctor_set(v_reuseFailAlloc_1260_, 11, v_dynlibs_1251_);
lean_ctor_set(v_reuseFailAlloc_1260_, 12, v_plugins_1252_);
lean_ctor_set_uint8(v_reuseFailAlloc_1260_, sizeof(void*)*13, v_buildType_1238_);
lean_ctor_set_uint8(v_reuseFailAlloc_1260_, sizeof(void*)*13 + 1, v_backend_1248_);
lean_ctor_set_uint8(v_reuseFailAlloc_1260_, sizeof(void*)*13 + 2, v_precompileImports_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1260_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1253_);
lean_ctor_set_uint8(v_reuseFailAlloc_1260_, sizeof(void*)*13 + 4, v_allowNonModules_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1263_, lean_object* v_cfg_1264_){
_start:
{
uint8_t v_buildType_1265_; lean_object* v_leanOptions_1266_; lean_object* v_moreLeanArgs_1267_; lean_object* v_weakLeanArgs_1268_; lean_object* v_moreLeancArgs_1269_; lean_object* v_moreServerOptions_1270_; lean_object* v_weakLeancArgs_1271_; lean_object* v_moreLinkObjs_1272_; lean_object* v_moreLinkLibs_1273_; lean_object* v_moreLinkArgs_1274_; lean_object* v_weakLinkArgs_1275_; uint8_t v_backend_1276_; lean_object* v_platformIndependent_1277_; uint8_t v_precompileImports_1278_; lean_object* v_dynlibs_1279_; lean_object* v_plugins_1280_; uint8_t v_requiresModuleSystem_1281_; uint8_t v_allowNonModules_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1290_; 
v_buildType_1265_ = lean_ctor_get_uint8(v_cfg_1264_, sizeof(void*)*13);
v_leanOptions_1266_ = lean_ctor_get(v_cfg_1264_, 0);
v_moreLeanArgs_1267_ = lean_ctor_get(v_cfg_1264_, 1);
v_weakLeanArgs_1268_ = lean_ctor_get(v_cfg_1264_, 2);
v_moreLeancArgs_1269_ = lean_ctor_get(v_cfg_1264_, 3);
v_moreServerOptions_1270_ = lean_ctor_get(v_cfg_1264_, 4);
v_weakLeancArgs_1271_ = lean_ctor_get(v_cfg_1264_, 5);
v_moreLinkObjs_1272_ = lean_ctor_get(v_cfg_1264_, 6);
v_moreLinkLibs_1273_ = lean_ctor_get(v_cfg_1264_, 7);
v_moreLinkArgs_1274_ = lean_ctor_get(v_cfg_1264_, 8);
v_weakLinkArgs_1275_ = lean_ctor_get(v_cfg_1264_, 9);
v_backend_1276_ = lean_ctor_get_uint8(v_cfg_1264_, sizeof(void*)*13 + 1);
v_platformIndependent_1277_ = lean_ctor_get(v_cfg_1264_, 10);
v_precompileImports_1278_ = lean_ctor_get_uint8(v_cfg_1264_, sizeof(void*)*13 + 2);
v_dynlibs_1279_ = lean_ctor_get(v_cfg_1264_, 11);
v_plugins_1280_ = lean_ctor_get(v_cfg_1264_, 12);
v_requiresModuleSystem_1281_ = lean_ctor_get_uint8(v_cfg_1264_, sizeof(void*)*13 + 3);
v_allowNonModules_1282_ = lean_ctor_get_uint8(v_cfg_1264_, sizeof(void*)*13 + 4);
v_isSharedCheck_1290_ = !lean_is_exclusive(v_cfg_1264_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1284_ = v_cfg_1264_;
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_plugins_1280_);
lean_inc(v_dynlibs_1279_);
lean_inc(v_platformIndependent_1277_);
lean_inc(v_weakLinkArgs_1275_);
lean_inc(v_moreLinkArgs_1274_);
lean_inc(v_moreLinkLibs_1273_);
lean_inc(v_moreLinkObjs_1272_);
lean_inc(v_weakLeancArgs_1271_);
lean_inc(v_moreServerOptions_1270_);
lean_inc(v_moreLeancArgs_1269_);
lean_inc(v_weakLeanArgs_1268_);
lean_inc(v_moreLeanArgs_1267_);
lean_inc(v_leanOptions_1266_);
lean_dec(v_cfg_1264_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1290_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_apply_1(v_f_1263_, v_moreLeanArgs_1267_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___x_1286_);
v___x_1288_ = v___x_1284_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_leanOptions_1266_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_weakLeanArgs_1268_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_moreLeancArgs_1269_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_moreServerOptions_1270_);
lean_ctor_set(v_reuseFailAlloc_1289_, 5, v_weakLeancArgs_1271_);
lean_ctor_set(v_reuseFailAlloc_1289_, 6, v_moreLinkObjs_1272_);
lean_ctor_set(v_reuseFailAlloc_1289_, 7, v_moreLinkLibs_1273_);
lean_ctor_set(v_reuseFailAlloc_1289_, 8, v_moreLinkArgs_1274_);
lean_ctor_set(v_reuseFailAlloc_1289_, 9, v_weakLinkArgs_1275_);
lean_ctor_set(v_reuseFailAlloc_1289_, 10, v_platformIndependent_1277_);
lean_ctor_set(v_reuseFailAlloc_1289_, 11, v_dynlibs_1279_);
lean_ctor_set(v_reuseFailAlloc_1289_, 12, v_plugins_1280_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*13, v_buildType_1265_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*13 + 1, v_backend_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*13 + 2, v_precompileImports_1278_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*13 + 4, v_allowNonModules_1282_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1291_){
_start:
{
lean_object* v___x_1292_; 
v___x_1292_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1293_);
lean_dec_ref(v_x_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1306_){
_start:
{
lean_object* v_weakLeanArgs_1307_; 
v_weakLeanArgs_1307_ = lean_ctor_get(v_cfg_1306_, 2);
lean_inc_ref(v_weakLeanArgs_1307_);
return v_weakLeanArgs_1307_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1308_);
lean_dec_ref(v_cfg_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1310_, lean_object* v_cfg_1311_){
_start:
{
uint8_t v_buildType_1312_; lean_object* v_leanOptions_1313_; lean_object* v_moreLeanArgs_1314_; lean_object* v_moreLeancArgs_1315_; lean_object* v_moreServerOptions_1316_; lean_object* v_weakLeancArgs_1317_; lean_object* v_moreLinkObjs_1318_; lean_object* v_moreLinkLibs_1319_; lean_object* v_moreLinkArgs_1320_; lean_object* v_weakLinkArgs_1321_; uint8_t v_backend_1322_; lean_object* v_platformIndependent_1323_; uint8_t v_precompileImports_1324_; lean_object* v_dynlibs_1325_; lean_object* v_plugins_1326_; uint8_t v_requiresModuleSystem_1327_; uint8_t v_allowNonModules_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_buildType_1312_ = lean_ctor_get_uint8(v_cfg_1311_, sizeof(void*)*13);
v_leanOptions_1313_ = lean_ctor_get(v_cfg_1311_, 0);
v_moreLeanArgs_1314_ = lean_ctor_get(v_cfg_1311_, 1);
v_moreLeancArgs_1315_ = lean_ctor_get(v_cfg_1311_, 3);
v_moreServerOptions_1316_ = lean_ctor_get(v_cfg_1311_, 4);
v_weakLeancArgs_1317_ = lean_ctor_get(v_cfg_1311_, 5);
v_moreLinkObjs_1318_ = lean_ctor_get(v_cfg_1311_, 6);
v_moreLinkLibs_1319_ = lean_ctor_get(v_cfg_1311_, 7);
v_moreLinkArgs_1320_ = lean_ctor_get(v_cfg_1311_, 8);
v_weakLinkArgs_1321_ = lean_ctor_get(v_cfg_1311_, 9);
v_backend_1322_ = lean_ctor_get_uint8(v_cfg_1311_, sizeof(void*)*13 + 1);
v_platformIndependent_1323_ = lean_ctor_get(v_cfg_1311_, 10);
v_precompileImports_1324_ = lean_ctor_get_uint8(v_cfg_1311_, sizeof(void*)*13 + 2);
v_dynlibs_1325_ = lean_ctor_get(v_cfg_1311_, 11);
v_plugins_1326_ = lean_ctor_get(v_cfg_1311_, 12);
v_requiresModuleSystem_1327_ = lean_ctor_get_uint8(v_cfg_1311_, sizeof(void*)*13 + 3);
v_allowNonModules_1328_ = lean_ctor_get_uint8(v_cfg_1311_, sizeof(void*)*13 + 4);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_cfg_1311_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v_cfg_1311_, 2);
lean_dec(v_unused_1336_);
v___x_1330_ = v_cfg_1311_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_plugins_1326_);
lean_inc(v_dynlibs_1325_);
lean_inc(v_platformIndependent_1323_);
lean_inc(v_weakLinkArgs_1321_);
lean_inc(v_moreLinkArgs_1320_);
lean_inc(v_moreLinkLibs_1319_);
lean_inc(v_moreLinkObjs_1318_);
lean_inc(v_weakLeancArgs_1317_);
lean_inc(v_moreServerOptions_1316_);
lean_inc(v_moreLeancArgs_1315_);
lean_inc(v_moreLeanArgs_1314_);
lean_inc(v_leanOptions_1313_);
lean_dec(v_cfg_1311_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 2, v_val_1310_);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_leanOptions_1313_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_moreLeanArgs_1314_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_val_1310_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_moreLeancArgs_1315_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_moreServerOptions_1316_);
lean_ctor_set(v_reuseFailAlloc_1334_, 5, v_weakLeancArgs_1317_);
lean_ctor_set(v_reuseFailAlloc_1334_, 6, v_moreLinkObjs_1318_);
lean_ctor_set(v_reuseFailAlloc_1334_, 7, v_moreLinkLibs_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 8, v_moreLinkArgs_1320_);
lean_ctor_set(v_reuseFailAlloc_1334_, 9, v_weakLinkArgs_1321_);
lean_ctor_set(v_reuseFailAlloc_1334_, 10, v_platformIndependent_1323_);
lean_ctor_set(v_reuseFailAlloc_1334_, 11, v_dynlibs_1325_);
lean_ctor_set(v_reuseFailAlloc_1334_, 12, v_plugins_1326_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*13, v_buildType_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*13 + 1, v_backend_1322_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*13 + 2, v_precompileImports_1324_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1327_);
lean_ctor_set_uint8(v_reuseFailAlloc_1334_, sizeof(void*)*13 + 4, v_allowNonModules_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1337_, lean_object* v_cfg_1338_){
_start:
{
uint8_t v_buildType_1339_; lean_object* v_leanOptions_1340_; lean_object* v_moreLeanArgs_1341_; lean_object* v_weakLeanArgs_1342_; lean_object* v_moreLeancArgs_1343_; lean_object* v_moreServerOptions_1344_; lean_object* v_weakLeancArgs_1345_; lean_object* v_moreLinkObjs_1346_; lean_object* v_moreLinkLibs_1347_; lean_object* v_moreLinkArgs_1348_; lean_object* v_weakLinkArgs_1349_; uint8_t v_backend_1350_; lean_object* v_platformIndependent_1351_; uint8_t v_precompileImports_1352_; lean_object* v_dynlibs_1353_; lean_object* v_plugins_1354_; uint8_t v_requiresModuleSystem_1355_; uint8_t v_allowNonModules_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1364_; 
v_buildType_1339_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*13);
v_leanOptions_1340_ = lean_ctor_get(v_cfg_1338_, 0);
v_moreLeanArgs_1341_ = lean_ctor_get(v_cfg_1338_, 1);
v_weakLeanArgs_1342_ = lean_ctor_get(v_cfg_1338_, 2);
v_moreLeancArgs_1343_ = lean_ctor_get(v_cfg_1338_, 3);
v_moreServerOptions_1344_ = lean_ctor_get(v_cfg_1338_, 4);
v_weakLeancArgs_1345_ = lean_ctor_get(v_cfg_1338_, 5);
v_moreLinkObjs_1346_ = lean_ctor_get(v_cfg_1338_, 6);
v_moreLinkLibs_1347_ = lean_ctor_get(v_cfg_1338_, 7);
v_moreLinkArgs_1348_ = lean_ctor_get(v_cfg_1338_, 8);
v_weakLinkArgs_1349_ = lean_ctor_get(v_cfg_1338_, 9);
v_backend_1350_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*13 + 1);
v_platformIndependent_1351_ = lean_ctor_get(v_cfg_1338_, 10);
v_precompileImports_1352_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*13 + 2);
v_dynlibs_1353_ = lean_ctor_get(v_cfg_1338_, 11);
v_plugins_1354_ = lean_ctor_get(v_cfg_1338_, 12);
v_requiresModuleSystem_1355_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*13 + 3);
v_allowNonModules_1356_ = lean_ctor_get_uint8(v_cfg_1338_, sizeof(void*)*13 + 4);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_cfg_1338_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1358_ = v_cfg_1338_;
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_plugins_1354_);
lean_inc(v_dynlibs_1353_);
lean_inc(v_platformIndependent_1351_);
lean_inc(v_weakLinkArgs_1349_);
lean_inc(v_moreLinkArgs_1348_);
lean_inc(v_moreLinkLibs_1347_);
lean_inc(v_moreLinkObjs_1346_);
lean_inc(v_weakLeancArgs_1345_);
lean_inc(v_moreServerOptions_1344_);
lean_inc(v_moreLeancArgs_1343_);
lean_inc(v_weakLeanArgs_1342_);
lean_inc(v_moreLeanArgs_1341_);
lean_inc(v_leanOptions_1340_);
lean_dec(v_cfg_1338_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1364_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1360_ = lean_apply_1(v_f_1337_, v_weakLeanArgs_1342_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 2, v___x_1360_);
v___x_1362_ = v___x_1358_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_leanOptions_1340_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_moreLeanArgs_1341_);
lean_ctor_set(v_reuseFailAlloc_1363_, 2, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1363_, 3, v_moreLeancArgs_1343_);
lean_ctor_set(v_reuseFailAlloc_1363_, 4, v_moreServerOptions_1344_);
lean_ctor_set(v_reuseFailAlloc_1363_, 5, v_weakLeancArgs_1345_);
lean_ctor_set(v_reuseFailAlloc_1363_, 6, v_moreLinkObjs_1346_);
lean_ctor_set(v_reuseFailAlloc_1363_, 7, v_moreLinkLibs_1347_);
lean_ctor_set(v_reuseFailAlloc_1363_, 8, v_moreLinkArgs_1348_);
lean_ctor_set(v_reuseFailAlloc_1363_, 9, v_weakLinkArgs_1349_);
lean_ctor_set(v_reuseFailAlloc_1363_, 10, v_platformIndependent_1351_);
lean_ctor_set(v_reuseFailAlloc_1363_, 11, v_dynlibs_1353_);
lean_ctor_set(v_reuseFailAlloc_1363_, 12, v_plugins_1354_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*13, v_buildType_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*13 + 1, v_backend_1350_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*13 + 2, v_precompileImports_1352_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1355_);
lean_ctor_set_uint8(v_reuseFailAlloc_1363_, sizeof(void*)*13 + 4, v_allowNonModules_1356_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1375_){
_start:
{
lean_object* v_moreLeancArgs_1376_; 
v_moreLeancArgs_1376_ = lean_ctor_get(v_cfg_1375_, 3);
lean_inc_ref(v_moreLeancArgs_1376_);
return v_moreLeancArgs_1376_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1377_);
lean_dec_ref(v_cfg_1377_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1379_, lean_object* v_cfg_1380_){
_start:
{
uint8_t v_buildType_1381_; lean_object* v_leanOptions_1382_; lean_object* v_moreLeanArgs_1383_; lean_object* v_weakLeanArgs_1384_; lean_object* v_moreServerOptions_1385_; lean_object* v_weakLeancArgs_1386_; lean_object* v_moreLinkObjs_1387_; lean_object* v_moreLinkLibs_1388_; lean_object* v_moreLinkArgs_1389_; lean_object* v_weakLinkArgs_1390_; uint8_t v_backend_1391_; lean_object* v_platformIndependent_1392_; uint8_t v_precompileImports_1393_; lean_object* v_dynlibs_1394_; lean_object* v_plugins_1395_; uint8_t v_requiresModuleSystem_1396_; uint8_t v_allowNonModules_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_buildType_1381_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*13);
v_leanOptions_1382_ = lean_ctor_get(v_cfg_1380_, 0);
v_moreLeanArgs_1383_ = lean_ctor_get(v_cfg_1380_, 1);
v_weakLeanArgs_1384_ = lean_ctor_get(v_cfg_1380_, 2);
v_moreServerOptions_1385_ = lean_ctor_get(v_cfg_1380_, 4);
v_weakLeancArgs_1386_ = lean_ctor_get(v_cfg_1380_, 5);
v_moreLinkObjs_1387_ = lean_ctor_get(v_cfg_1380_, 6);
v_moreLinkLibs_1388_ = lean_ctor_get(v_cfg_1380_, 7);
v_moreLinkArgs_1389_ = lean_ctor_get(v_cfg_1380_, 8);
v_weakLinkArgs_1390_ = lean_ctor_get(v_cfg_1380_, 9);
v_backend_1391_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*13 + 1);
v_platformIndependent_1392_ = lean_ctor_get(v_cfg_1380_, 10);
v_precompileImports_1393_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*13 + 2);
v_dynlibs_1394_ = lean_ctor_get(v_cfg_1380_, 11);
v_plugins_1395_ = lean_ctor_get(v_cfg_1380_, 12);
v_requiresModuleSystem_1396_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*13 + 3);
v_allowNonModules_1397_ = lean_ctor_get_uint8(v_cfg_1380_, sizeof(void*)*13 + 4);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_cfg_1380_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; 
v_unused_1405_ = lean_ctor_get(v_cfg_1380_, 3);
lean_dec(v_unused_1405_);
v___x_1399_ = v_cfg_1380_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_plugins_1395_);
lean_inc(v_dynlibs_1394_);
lean_inc(v_platformIndependent_1392_);
lean_inc(v_weakLinkArgs_1390_);
lean_inc(v_moreLinkArgs_1389_);
lean_inc(v_moreLinkLibs_1388_);
lean_inc(v_moreLinkObjs_1387_);
lean_inc(v_weakLeancArgs_1386_);
lean_inc(v_moreServerOptions_1385_);
lean_inc(v_weakLeanArgs_1384_);
lean_inc(v_moreLeanArgs_1383_);
lean_inc(v_leanOptions_1382_);
lean_dec(v_cfg_1380_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
lean_ctor_set(v___x_1399_, 3, v_val_1379_);
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_leanOptions_1382_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_moreLeanArgs_1383_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_weakLeanArgs_1384_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_val_1379_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_moreServerOptions_1385_);
lean_ctor_set(v_reuseFailAlloc_1403_, 5, v_weakLeancArgs_1386_);
lean_ctor_set(v_reuseFailAlloc_1403_, 6, v_moreLinkObjs_1387_);
lean_ctor_set(v_reuseFailAlloc_1403_, 7, v_moreLinkLibs_1388_);
lean_ctor_set(v_reuseFailAlloc_1403_, 8, v_moreLinkArgs_1389_);
lean_ctor_set(v_reuseFailAlloc_1403_, 9, v_weakLinkArgs_1390_);
lean_ctor_set(v_reuseFailAlloc_1403_, 10, v_platformIndependent_1392_);
lean_ctor_set(v_reuseFailAlloc_1403_, 11, v_dynlibs_1394_);
lean_ctor_set(v_reuseFailAlloc_1403_, 12, v_plugins_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13, v_buildType_1381_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 1, v_backend_1391_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 2, v_precompileImports_1393_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1403_, sizeof(void*)*13 + 4, v_allowNonModules_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1406_, lean_object* v_cfg_1407_){
_start:
{
uint8_t v_buildType_1408_; lean_object* v_leanOptions_1409_; lean_object* v_moreLeanArgs_1410_; lean_object* v_weakLeanArgs_1411_; lean_object* v_moreLeancArgs_1412_; lean_object* v_moreServerOptions_1413_; lean_object* v_weakLeancArgs_1414_; lean_object* v_moreLinkObjs_1415_; lean_object* v_moreLinkLibs_1416_; lean_object* v_moreLinkArgs_1417_; lean_object* v_weakLinkArgs_1418_; uint8_t v_backend_1419_; lean_object* v_platformIndependent_1420_; uint8_t v_precompileImports_1421_; lean_object* v_dynlibs_1422_; lean_object* v_plugins_1423_; uint8_t v_requiresModuleSystem_1424_; uint8_t v_allowNonModules_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1433_; 
v_buildType_1408_ = lean_ctor_get_uint8(v_cfg_1407_, sizeof(void*)*13);
v_leanOptions_1409_ = lean_ctor_get(v_cfg_1407_, 0);
v_moreLeanArgs_1410_ = lean_ctor_get(v_cfg_1407_, 1);
v_weakLeanArgs_1411_ = lean_ctor_get(v_cfg_1407_, 2);
v_moreLeancArgs_1412_ = lean_ctor_get(v_cfg_1407_, 3);
v_moreServerOptions_1413_ = lean_ctor_get(v_cfg_1407_, 4);
v_weakLeancArgs_1414_ = lean_ctor_get(v_cfg_1407_, 5);
v_moreLinkObjs_1415_ = lean_ctor_get(v_cfg_1407_, 6);
v_moreLinkLibs_1416_ = lean_ctor_get(v_cfg_1407_, 7);
v_moreLinkArgs_1417_ = lean_ctor_get(v_cfg_1407_, 8);
v_weakLinkArgs_1418_ = lean_ctor_get(v_cfg_1407_, 9);
v_backend_1419_ = lean_ctor_get_uint8(v_cfg_1407_, sizeof(void*)*13 + 1);
v_platformIndependent_1420_ = lean_ctor_get(v_cfg_1407_, 10);
v_precompileImports_1421_ = lean_ctor_get_uint8(v_cfg_1407_, sizeof(void*)*13 + 2);
v_dynlibs_1422_ = lean_ctor_get(v_cfg_1407_, 11);
v_plugins_1423_ = lean_ctor_get(v_cfg_1407_, 12);
v_requiresModuleSystem_1424_ = lean_ctor_get_uint8(v_cfg_1407_, sizeof(void*)*13 + 3);
v_allowNonModules_1425_ = lean_ctor_get_uint8(v_cfg_1407_, sizeof(void*)*13 + 4);
v_isSharedCheck_1433_ = !lean_is_exclusive(v_cfg_1407_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1427_ = v_cfg_1407_;
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_plugins_1423_);
lean_inc(v_dynlibs_1422_);
lean_inc(v_platformIndependent_1420_);
lean_inc(v_weakLinkArgs_1418_);
lean_inc(v_moreLinkArgs_1417_);
lean_inc(v_moreLinkLibs_1416_);
lean_inc(v_moreLinkObjs_1415_);
lean_inc(v_weakLeancArgs_1414_);
lean_inc(v_moreServerOptions_1413_);
lean_inc(v_moreLeancArgs_1412_);
lean_inc(v_weakLeanArgs_1411_);
lean_inc(v_moreLeanArgs_1410_);
lean_inc(v_leanOptions_1409_);
lean_dec(v_cfg_1407_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1433_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1429_ = lean_apply_1(v_f_1406_, v_moreLeancArgs_1412_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 3, v___x_1429_);
v___x_1431_ = v___x_1427_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_leanOptions_1409_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_moreLeanArgs_1410_);
lean_ctor_set(v_reuseFailAlloc_1432_, 2, v_weakLeanArgs_1411_);
lean_ctor_set(v_reuseFailAlloc_1432_, 3, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1432_, 4, v_moreServerOptions_1413_);
lean_ctor_set(v_reuseFailAlloc_1432_, 5, v_weakLeancArgs_1414_);
lean_ctor_set(v_reuseFailAlloc_1432_, 6, v_moreLinkObjs_1415_);
lean_ctor_set(v_reuseFailAlloc_1432_, 7, v_moreLinkLibs_1416_);
lean_ctor_set(v_reuseFailAlloc_1432_, 8, v_moreLinkArgs_1417_);
lean_ctor_set(v_reuseFailAlloc_1432_, 9, v_weakLinkArgs_1418_);
lean_ctor_set(v_reuseFailAlloc_1432_, 10, v_platformIndependent_1420_);
lean_ctor_set(v_reuseFailAlloc_1432_, 11, v_dynlibs_1422_);
lean_ctor_set(v_reuseFailAlloc_1432_, 12, v_plugins_1423_);
lean_ctor_set_uint8(v_reuseFailAlloc_1432_, sizeof(void*)*13, v_buildType_1408_);
lean_ctor_set_uint8(v_reuseFailAlloc_1432_, sizeof(void*)*13 + 1, v_backend_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1432_, sizeof(void*)*13 + 2, v_precompileImports_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1432_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1424_);
lean_ctor_set_uint8(v_reuseFailAlloc_1432_, sizeof(void*)*13 + 4, v_allowNonModules_1425_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1444_){
_start:
{
lean_object* v_moreServerOptions_1445_; 
v_moreServerOptions_1445_ = lean_ctor_get(v_cfg_1444_, 4);
lean_inc_ref(v_moreServerOptions_1445_);
return v_moreServerOptions_1445_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1446_);
lean_dec_ref(v_cfg_1446_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1448_, lean_object* v_cfg_1449_){
_start:
{
uint8_t v_buildType_1450_; lean_object* v_leanOptions_1451_; lean_object* v_moreLeanArgs_1452_; lean_object* v_weakLeanArgs_1453_; lean_object* v_moreLeancArgs_1454_; lean_object* v_weakLeancArgs_1455_; lean_object* v_moreLinkObjs_1456_; lean_object* v_moreLinkLibs_1457_; lean_object* v_moreLinkArgs_1458_; lean_object* v_weakLinkArgs_1459_; uint8_t v_backend_1460_; lean_object* v_platformIndependent_1461_; uint8_t v_precompileImports_1462_; lean_object* v_dynlibs_1463_; lean_object* v_plugins_1464_; uint8_t v_requiresModuleSystem_1465_; uint8_t v_allowNonModules_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
v_buildType_1450_ = lean_ctor_get_uint8(v_cfg_1449_, sizeof(void*)*13);
v_leanOptions_1451_ = lean_ctor_get(v_cfg_1449_, 0);
v_moreLeanArgs_1452_ = lean_ctor_get(v_cfg_1449_, 1);
v_weakLeanArgs_1453_ = lean_ctor_get(v_cfg_1449_, 2);
v_moreLeancArgs_1454_ = lean_ctor_get(v_cfg_1449_, 3);
v_weakLeancArgs_1455_ = lean_ctor_get(v_cfg_1449_, 5);
v_moreLinkObjs_1456_ = lean_ctor_get(v_cfg_1449_, 6);
v_moreLinkLibs_1457_ = lean_ctor_get(v_cfg_1449_, 7);
v_moreLinkArgs_1458_ = lean_ctor_get(v_cfg_1449_, 8);
v_weakLinkArgs_1459_ = lean_ctor_get(v_cfg_1449_, 9);
v_backend_1460_ = lean_ctor_get_uint8(v_cfg_1449_, sizeof(void*)*13 + 1);
v_platformIndependent_1461_ = lean_ctor_get(v_cfg_1449_, 10);
v_precompileImports_1462_ = lean_ctor_get_uint8(v_cfg_1449_, sizeof(void*)*13 + 2);
v_dynlibs_1463_ = lean_ctor_get(v_cfg_1449_, 11);
v_plugins_1464_ = lean_ctor_get(v_cfg_1449_, 12);
v_requiresModuleSystem_1465_ = lean_ctor_get_uint8(v_cfg_1449_, sizeof(void*)*13 + 3);
v_allowNonModules_1466_ = lean_ctor_get_uint8(v_cfg_1449_, sizeof(void*)*13 + 4);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_cfg_1449_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; 
v_unused_1474_ = lean_ctor_get(v_cfg_1449_, 4);
lean_dec(v_unused_1474_);
v___x_1468_ = v_cfg_1449_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_plugins_1464_);
lean_inc(v_dynlibs_1463_);
lean_inc(v_platformIndependent_1461_);
lean_inc(v_weakLinkArgs_1459_);
lean_inc(v_moreLinkArgs_1458_);
lean_inc(v_moreLinkLibs_1457_);
lean_inc(v_moreLinkObjs_1456_);
lean_inc(v_weakLeancArgs_1455_);
lean_inc(v_moreLeancArgs_1454_);
lean_inc(v_weakLeanArgs_1453_);
lean_inc(v_moreLeanArgs_1452_);
lean_inc(v_leanOptions_1451_);
lean_dec(v_cfg_1449_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 4, v_val_1448_);
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_leanOptions_1451_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_moreLeanArgs_1452_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_weakLeanArgs_1453_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_moreLeancArgs_1454_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_val_1448_);
lean_ctor_set(v_reuseFailAlloc_1472_, 5, v_weakLeancArgs_1455_);
lean_ctor_set(v_reuseFailAlloc_1472_, 6, v_moreLinkObjs_1456_);
lean_ctor_set(v_reuseFailAlloc_1472_, 7, v_moreLinkLibs_1457_);
lean_ctor_set(v_reuseFailAlloc_1472_, 8, v_moreLinkArgs_1458_);
lean_ctor_set(v_reuseFailAlloc_1472_, 9, v_weakLinkArgs_1459_);
lean_ctor_set(v_reuseFailAlloc_1472_, 10, v_platformIndependent_1461_);
lean_ctor_set(v_reuseFailAlloc_1472_, 11, v_dynlibs_1463_);
lean_ctor_set(v_reuseFailAlloc_1472_, 12, v_plugins_1464_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*13, v_buildType_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*13 + 1, v_backend_1460_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*13 + 2, v_precompileImports_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1465_);
lean_ctor_set_uint8(v_reuseFailAlloc_1472_, sizeof(void*)*13 + 4, v_allowNonModules_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1475_, lean_object* v_cfg_1476_){
_start:
{
uint8_t v_buildType_1477_; lean_object* v_leanOptions_1478_; lean_object* v_moreLeanArgs_1479_; lean_object* v_weakLeanArgs_1480_; lean_object* v_moreLeancArgs_1481_; lean_object* v_moreServerOptions_1482_; lean_object* v_weakLeancArgs_1483_; lean_object* v_moreLinkObjs_1484_; lean_object* v_moreLinkLibs_1485_; lean_object* v_moreLinkArgs_1486_; lean_object* v_weakLinkArgs_1487_; uint8_t v_backend_1488_; lean_object* v_platformIndependent_1489_; uint8_t v_precompileImports_1490_; lean_object* v_dynlibs_1491_; lean_object* v_plugins_1492_; uint8_t v_requiresModuleSystem_1493_; uint8_t v_allowNonModules_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1502_; 
v_buildType_1477_ = lean_ctor_get_uint8(v_cfg_1476_, sizeof(void*)*13);
v_leanOptions_1478_ = lean_ctor_get(v_cfg_1476_, 0);
v_moreLeanArgs_1479_ = lean_ctor_get(v_cfg_1476_, 1);
v_weakLeanArgs_1480_ = lean_ctor_get(v_cfg_1476_, 2);
v_moreLeancArgs_1481_ = lean_ctor_get(v_cfg_1476_, 3);
v_moreServerOptions_1482_ = lean_ctor_get(v_cfg_1476_, 4);
v_weakLeancArgs_1483_ = lean_ctor_get(v_cfg_1476_, 5);
v_moreLinkObjs_1484_ = lean_ctor_get(v_cfg_1476_, 6);
v_moreLinkLibs_1485_ = lean_ctor_get(v_cfg_1476_, 7);
v_moreLinkArgs_1486_ = lean_ctor_get(v_cfg_1476_, 8);
v_weakLinkArgs_1487_ = lean_ctor_get(v_cfg_1476_, 9);
v_backend_1488_ = lean_ctor_get_uint8(v_cfg_1476_, sizeof(void*)*13 + 1);
v_platformIndependent_1489_ = lean_ctor_get(v_cfg_1476_, 10);
v_precompileImports_1490_ = lean_ctor_get_uint8(v_cfg_1476_, sizeof(void*)*13 + 2);
v_dynlibs_1491_ = lean_ctor_get(v_cfg_1476_, 11);
v_plugins_1492_ = lean_ctor_get(v_cfg_1476_, 12);
v_requiresModuleSystem_1493_ = lean_ctor_get_uint8(v_cfg_1476_, sizeof(void*)*13 + 3);
v_allowNonModules_1494_ = lean_ctor_get_uint8(v_cfg_1476_, sizeof(void*)*13 + 4);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_cfg_1476_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1496_ = v_cfg_1476_;
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_plugins_1492_);
lean_inc(v_dynlibs_1491_);
lean_inc(v_platformIndependent_1489_);
lean_inc(v_weakLinkArgs_1487_);
lean_inc(v_moreLinkArgs_1486_);
lean_inc(v_moreLinkLibs_1485_);
lean_inc(v_moreLinkObjs_1484_);
lean_inc(v_weakLeancArgs_1483_);
lean_inc(v_moreServerOptions_1482_);
lean_inc(v_moreLeancArgs_1481_);
lean_inc(v_weakLeanArgs_1480_);
lean_inc(v_moreLeanArgs_1479_);
lean_inc(v_leanOptions_1478_);
lean_dec(v_cfg_1476_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1502_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1500_; 
v___x_1498_ = lean_apply_1(v_f_1475_, v_moreServerOptions_1482_);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 4, v___x_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_leanOptions_1478_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_moreLeanArgs_1479_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_weakLeanArgs_1480_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_moreLeancArgs_1481_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1501_, 5, v_weakLeancArgs_1483_);
lean_ctor_set(v_reuseFailAlloc_1501_, 6, v_moreLinkObjs_1484_);
lean_ctor_set(v_reuseFailAlloc_1501_, 7, v_moreLinkLibs_1485_);
lean_ctor_set(v_reuseFailAlloc_1501_, 8, v_moreLinkArgs_1486_);
lean_ctor_set(v_reuseFailAlloc_1501_, 9, v_weakLinkArgs_1487_);
lean_ctor_set(v_reuseFailAlloc_1501_, 10, v_platformIndependent_1489_);
lean_ctor_set(v_reuseFailAlloc_1501_, 11, v_dynlibs_1491_);
lean_ctor_set(v_reuseFailAlloc_1501_, 12, v_plugins_1492_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*13, v_buildType_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*13 + 1, v_backend_1488_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*13 + 2, v_precompileImports_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1501_, sizeof(void*)*13 + 4, v_allowNonModules_1494_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1513_){
_start:
{
lean_object* v_weakLeancArgs_1514_; 
v_weakLeancArgs_1514_ = lean_ctor_get(v_cfg_1513_, 5);
lean_inc_ref(v_weakLeancArgs_1514_);
return v_weakLeancArgs_1514_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1515_);
lean_dec_ref(v_cfg_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1517_, lean_object* v_cfg_1518_){
_start:
{
uint8_t v_buildType_1519_; lean_object* v_leanOptions_1520_; lean_object* v_moreLeanArgs_1521_; lean_object* v_weakLeanArgs_1522_; lean_object* v_moreLeancArgs_1523_; lean_object* v_moreServerOptions_1524_; lean_object* v_moreLinkObjs_1525_; lean_object* v_moreLinkLibs_1526_; lean_object* v_moreLinkArgs_1527_; lean_object* v_weakLinkArgs_1528_; uint8_t v_backend_1529_; lean_object* v_platformIndependent_1530_; uint8_t v_precompileImports_1531_; lean_object* v_dynlibs_1532_; lean_object* v_plugins_1533_; uint8_t v_requiresModuleSystem_1534_; uint8_t v_allowNonModules_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_buildType_1519_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13);
v_leanOptions_1520_ = lean_ctor_get(v_cfg_1518_, 0);
v_moreLeanArgs_1521_ = lean_ctor_get(v_cfg_1518_, 1);
v_weakLeanArgs_1522_ = lean_ctor_get(v_cfg_1518_, 2);
v_moreLeancArgs_1523_ = lean_ctor_get(v_cfg_1518_, 3);
v_moreServerOptions_1524_ = lean_ctor_get(v_cfg_1518_, 4);
v_moreLinkObjs_1525_ = lean_ctor_get(v_cfg_1518_, 6);
v_moreLinkLibs_1526_ = lean_ctor_get(v_cfg_1518_, 7);
v_moreLinkArgs_1527_ = lean_ctor_get(v_cfg_1518_, 8);
v_weakLinkArgs_1528_ = lean_ctor_get(v_cfg_1518_, 9);
v_backend_1529_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13 + 1);
v_platformIndependent_1530_ = lean_ctor_get(v_cfg_1518_, 10);
v_precompileImports_1531_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13 + 2);
v_dynlibs_1532_ = lean_ctor_get(v_cfg_1518_, 11);
v_plugins_1533_ = lean_ctor_get(v_cfg_1518_, 12);
v_requiresModuleSystem_1534_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13 + 3);
v_allowNonModules_1535_ = lean_ctor_get_uint8(v_cfg_1518_, sizeof(void*)*13 + 4);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_cfg_1518_);
if (v_isSharedCheck_1542_ == 0)
{
lean_object* v_unused_1543_; 
v_unused_1543_ = lean_ctor_get(v_cfg_1518_, 5);
lean_dec(v_unused_1543_);
v___x_1537_ = v_cfg_1518_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_plugins_1533_);
lean_inc(v_dynlibs_1532_);
lean_inc(v_platformIndependent_1530_);
lean_inc(v_weakLinkArgs_1528_);
lean_inc(v_moreLinkArgs_1527_);
lean_inc(v_moreLinkLibs_1526_);
lean_inc(v_moreLinkObjs_1525_);
lean_inc(v_moreServerOptions_1524_);
lean_inc(v_moreLeancArgs_1523_);
lean_inc(v_weakLeanArgs_1522_);
lean_inc(v_moreLeanArgs_1521_);
lean_inc(v_leanOptions_1520_);
lean_dec(v_cfg_1518_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 5, v_val_1517_);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_leanOptions_1520_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_moreLeanArgs_1521_);
lean_ctor_set(v_reuseFailAlloc_1541_, 2, v_weakLeanArgs_1522_);
lean_ctor_set(v_reuseFailAlloc_1541_, 3, v_moreLeancArgs_1523_);
lean_ctor_set(v_reuseFailAlloc_1541_, 4, v_moreServerOptions_1524_);
lean_ctor_set(v_reuseFailAlloc_1541_, 5, v_val_1517_);
lean_ctor_set(v_reuseFailAlloc_1541_, 6, v_moreLinkObjs_1525_);
lean_ctor_set(v_reuseFailAlloc_1541_, 7, v_moreLinkLibs_1526_);
lean_ctor_set(v_reuseFailAlloc_1541_, 8, v_moreLinkArgs_1527_);
lean_ctor_set(v_reuseFailAlloc_1541_, 9, v_weakLinkArgs_1528_);
lean_ctor_set(v_reuseFailAlloc_1541_, 10, v_platformIndependent_1530_);
lean_ctor_set(v_reuseFailAlloc_1541_, 11, v_dynlibs_1532_);
lean_ctor_set(v_reuseFailAlloc_1541_, 12, v_plugins_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*13, v_buildType_1519_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*13 + 1, v_backend_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*13 + 2, v_precompileImports_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1541_, sizeof(void*)*13 + 4, v_allowNonModules_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1544_, lean_object* v_cfg_1545_){
_start:
{
uint8_t v_buildType_1546_; lean_object* v_leanOptions_1547_; lean_object* v_moreLeanArgs_1548_; lean_object* v_weakLeanArgs_1549_; lean_object* v_moreLeancArgs_1550_; lean_object* v_moreServerOptions_1551_; lean_object* v_weakLeancArgs_1552_; lean_object* v_moreLinkObjs_1553_; lean_object* v_moreLinkLibs_1554_; lean_object* v_moreLinkArgs_1555_; lean_object* v_weakLinkArgs_1556_; uint8_t v_backend_1557_; lean_object* v_platformIndependent_1558_; uint8_t v_precompileImports_1559_; lean_object* v_dynlibs_1560_; lean_object* v_plugins_1561_; uint8_t v_requiresModuleSystem_1562_; uint8_t v_allowNonModules_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1571_; 
v_buildType_1546_ = lean_ctor_get_uint8(v_cfg_1545_, sizeof(void*)*13);
v_leanOptions_1547_ = lean_ctor_get(v_cfg_1545_, 0);
v_moreLeanArgs_1548_ = lean_ctor_get(v_cfg_1545_, 1);
v_weakLeanArgs_1549_ = lean_ctor_get(v_cfg_1545_, 2);
v_moreLeancArgs_1550_ = lean_ctor_get(v_cfg_1545_, 3);
v_moreServerOptions_1551_ = lean_ctor_get(v_cfg_1545_, 4);
v_weakLeancArgs_1552_ = lean_ctor_get(v_cfg_1545_, 5);
v_moreLinkObjs_1553_ = lean_ctor_get(v_cfg_1545_, 6);
v_moreLinkLibs_1554_ = lean_ctor_get(v_cfg_1545_, 7);
v_moreLinkArgs_1555_ = lean_ctor_get(v_cfg_1545_, 8);
v_weakLinkArgs_1556_ = lean_ctor_get(v_cfg_1545_, 9);
v_backend_1557_ = lean_ctor_get_uint8(v_cfg_1545_, sizeof(void*)*13 + 1);
v_platformIndependent_1558_ = lean_ctor_get(v_cfg_1545_, 10);
v_precompileImports_1559_ = lean_ctor_get_uint8(v_cfg_1545_, sizeof(void*)*13 + 2);
v_dynlibs_1560_ = lean_ctor_get(v_cfg_1545_, 11);
v_plugins_1561_ = lean_ctor_get(v_cfg_1545_, 12);
v_requiresModuleSystem_1562_ = lean_ctor_get_uint8(v_cfg_1545_, sizeof(void*)*13 + 3);
v_allowNonModules_1563_ = lean_ctor_get_uint8(v_cfg_1545_, sizeof(void*)*13 + 4);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_cfg_1545_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1565_ = v_cfg_1545_;
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_plugins_1561_);
lean_inc(v_dynlibs_1560_);
lean_inc(v_platformIndependent_1558_);
lean_inc(v_weakLinkArgs_1556_);
lean_inc(v_moreLinkArgs_1555_);
lean_inc(v_moreLinkLibs_1554_);
lean_inc(v_moreLinkObjs_1553_);
lean_inc(v_weakLeancArgs_1552_);
lean_inc(v_moreServerOptions_1551_);
lean_inc(v_moreLeancArgs_1550_);
lean_inc(v_weakLeanArgs_1549_);
lean_inc(v_moreLeanArgs_1548_);
lean_inc(v_leanOptions_1547_);
lean_dec(v_cfg_1545_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1571_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
v___x_1567_ = lean_apply_1(v_f_1544_, v_weakLeancArgs_1552_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 5, v___x_1567_);
v___x_1569_ = v___x_1565_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_leanOptions_1547_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_moreLeanArgs_1548_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_weakLeanArgs_1549_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_moreLeancArgs_1550_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_moreServerOptions_1551_);
lean_ctor_set(v_reuseFailAlloc_1570_, 5, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1570_, 6, v_moreLinkObjs_1553_);
lean_ctor_set(v_reuseFailAlloc_1570_, 7, v_moreLinkLibs_1554_);
lean_ctor_set(v_reuseFailAlloc_1570_, 8, v_moreLinkArgs_1555_);
lean_ctor_set(v_reuseFailAlloc_1570_, 9, v_weakLinkArgs_1556_);
lean_ctor_set(v_reuseFailAlloc_1570_, 10, v_platformIndependent_1558_);
lean_ctor_set(v_reuseFailAlloc_1570_, 11, v_dynlibs_1560_);
lean_ctor_set(v_reuseFailAlloc_1570_, 12, v_plugins_1561_);
lean_ctor_set_uint8(v_reuseFailAlloc_1570_, sizeof(void*)*13, v_buildType_1546_);
lean_ctor_set_uint8(v_reuseFailAlloc_1570_, sizeof(void*)*13 + 1, v_backend_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1570_, sizeof(void*)*13 + 2, v_precompileImports_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1570_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1570_, sizeof(void*)*13 + 4, v_allowNonModules_1563_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1582_){
_start:
{
lean_object* v_moreLinkObjs_1583_; 
v_moreLinkObjs_1583_ = lean_ctor_get(v_cfg_1582_, 6);
lean_inc_ref(v_moreLinkObjs_1583_);
return v_moreLinkObjs_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1584_);
lean_dec_ref(v_cfg_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1586_, lean_object* v_cfg_1587_){
_start:
{
uint8_t v_buildType_1588_; lean_object* v_leanOptions_1589_; lean_object* v_moreLeanArgs_1590_; lean_object* v_weakLeanArgs_1591_; lean_object* v_moreLeancArgs_1592_; lean_object* v_moreServerOptions_1593_; lean_object* v_weakLeancArgs_1594_; lean_object* v_moreLinkLibs_1595_; lean_object* v_moreLinkArgs_1596_; lean_object* v_weakLinkArgs_1597_; uint8_t v_backend_1598_; lean_object* v_platformIndependent_1599_; uint8_t v_precompileImports_1600_; lean_object* v_dynlibs_1601_; lean_object* v_plugins_1602_; uint8_t v_requiresModuleSystem_1603_; uint8_t v_allowNonModules_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_buildType_1588_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*13);
v_leanOptions_1589_ = lean_ctor_get(v_cfg_1587_, 0);
v_moreLeanArgs_1590_ = lean_ctor_get(v_cfg_1587_, 1);
v_weakLeanArgs_1591_ = lean_ctor_get(v_cfg_1587_, 2);
v_moreLeancArgs_1592_ = lean_ctor_get(v_cfg_1587_, 3);
v_moreServerOptions_1593_ = lean_ctor_get(v_cfg_1587_, 4);
v_weakLeancArgs_1594_ = lean_ctor_get(v_cfg_1587_, 5);
v_moreLinkLibs_1595_ = lean_ctor_get(v_cfg_1587_, 7);
v_moreLinkArgs_1596_ = lean_ctor_get(v_cfg_1587_, 8);
v_weakLinkArgs_1597_ = lean_ctor_get(v_cfg_1587_, 9);
v_backend_1598_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*13 + 1);
v_platformIndependent_1599_ = lean_ctor_get(v_cfg_1587_, 10);
v_precompileImports_1600_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*13 + 2);
v_dynlibs_1601_ = lean_ctor_get(v_cfg_1587_, 11);
v_plugins_1602_ = lean_ctor_get(v_cfg_1587_, 12);
v_requiresModuleSystem_1603_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*13 + 3);
v_allowNonModules_1604_ = lean_ctor_get_uint8(v_cfg_1587_, sizeof(void*)*13 + 4);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_cfg_1587_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v_cfg_1587_, 6);
lean_dec(v_unused_1612_);
v___x_1606_ = v_cfg_1587_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_plugins_1602_);
lean_inc(v_dynlibs_1601_);
lean_inc(v_platformIndependent_1599_);
lean_inc(v_weakLinkArgs_1597_);
lean_inc(v_moreLinkArgs_1596_);
lean_inc(v_moreLinkLibs_1595_);
lean_inc(v_weakLeancArgs_1594_);
lean_inc(v_moreServerOptions_1593_);
lean_inc(v_moreLeancArgs_1592_);
lean_inc(v_weakLeanArgs_1591_);
lean_inc(v_moreLeanArgs_1590_);
lean_inc(v_leanOptions_1589_);
lean_dec(v_cfg_1587_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 6, v_val_1586_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_leanOptions_1589_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_moreLeanArgs_1590_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_weakLeanArgs_1591_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_moreLeancArgs_1592_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_moreServerOptions_1593_);
lean_ctor_set(v_reuseFailAlloc_1610_, 5, v_weakLeancArgs_1594_);
lean_ctor_set(v_reuseFailAlloc_1610_, 6, v_val_1586_);
lean_ctor_set(v_reuseFailAlloc_1610_, 7, v_moreLinkLibs_1595_);
lean_ctor_set(v_reuseFailAlloc_1610_, 8, v_moreLinkArgs_1596_);
lean_ctor_set(v_reuseFailAlloc_1610_, 9, v_weakLinkArgs_1597_);
lean_ctor_set(v_reuseFailAlloc_1610_, 10, v_platformIndependent_1599_);
lean_ctor_set(v_reuseFailAlloc_1610_, 11, v_dynlibs_1601_);
lean_ctor_set(v_reuseFailAlloc_1610_, 12, v_plugins_1602_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13, v_buildType_1588_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13 + 1, v_backend_1598_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13 + 2, v_precompileImports_1600_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1610_, sizeof(void*)*13 + 4, v_allowNonModules_1604_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1613_, lean_object* v_cfg_1614_){
_start:
{
uint8_t v_buildType_1615_; lean_object* v_leanOptions_1616_; lean_object* v_moreLeanArgs_1617_; lean_object* v_weakLeanArgs_1618_; lean_object* v_moreLeancArgs_1619_; lean_object* v_moreServerOptions_1620_; lean_object* v_weakLeancArgs_1621_; lean_object* v_moreLinkObjs_1622_; lean_object* v_moreLinkLibs_1623_; lean_object* v_moreLinkArgs_1624_; lean_object* v_weakLinkArgs_1625_; uint8_t v_backend_1626_; lean_object* v_platformIndependent_1627_; uint8_t v_precompileImports_1628_; lean_object* v_dynlibs_1629_; lean_object* v_plugins_1630_; uint8_t v_requiresModuleSystem_1631_; uint8_t v_allowNonModules_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1640_; 
v_buildType_1615_ = lean_ctor_get_uint8(v_cfg_1614_, sizeof(void*)*13);
v_leanOptions_1616_ = lean_ctor_get(v_cfg_1614_, 0);
v_moreLeanArgs_1617_ = lean_ctor_get(v_cfg_1614_, 1);
v_weakLeanArgs_1618_ = lean_ctor_get(v_cfg_1614_, 2);
v_moreLeancArgs_1619_ = lean_ctor_get(v_cfg_1614_, 3);
v_moreServerOptions_1620_ = lean_ctor_get(v_cfg_1614_, 4);
v_weakLeancArgs_1621_ = lean_ctor_get(v_cfg_1614_, 5);
v_moreLinkObjs_1622_ = lean_ctor_get(v_cfg_1614_, 6);
v_moreLinkLibs_1623_ = lean_ctor_get(v_cfg_1614_, 7);
v_moreLinkArgs_1624_ = lean_ctor_get(v_cfg_1614_, 8);
v_weakLinkArgs_1625_ = lean_ctor_get(v_cfg_1614_, 9);
v_backend_1626_ = lean_ctor_get_uint8(v_cfg_1614_, sizeof(void*)*13 + 1);
v_platformIndependent_1627_ = lean_ctor_get(v_cfg_1614_, 10);
v_precompileImports_1628_ = lean_ctor_get_uint8(v_cfg_1614_, sizeof(void*)*13 + 2);
v_dynlibs_1629_ = lean_ctor_get(v_cfg_1614_, 11);
v_plugins_1630_ = lean_ctor_get(v_cfg_1614_, 12);
v_requiresModuleSystem_1631_ = lean_ctor_get_uint8(v_cfg_1614_, sizeof(void*)*13 + 3);
v_allowNonModules_1632_ = lean_ctor_get_uint8(v_cfg_1614_, sizeof(void*)*13 + 4);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_cfg_1614_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1634_ = v_cfg_1614_;
v_isShared_1635_ = v_isSharedCheck_1640_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_plugins_1630_);
lean_inc(v_dynlibs_1629_);
lean_inc(v_platformIndependent_1627_);
lean_inc(v_weakLinkArgs_1625_);
lean_inc(v_moreLinkArgs_1624_);
lean_inc(v_moreLinkLibs_1623_);
lean_inc(v_moreLinkObjs_1622_);
lean_inc(v_weakLeancArgs_1621_);
lean_inc(v_moreServerOptions_1620_);
lean_inc(v_moreLeancArgs_1619_);
lean_inc(v_weakLeanArgs_1618_);
lean_inc(v_moreLeanArgs_1617_);
lean_inc(v_leanOptions_1616_);
lean_dec(v_cfg_1614_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1640_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = lean_apply_1(v_f_1613_, v_moreLinkObjs_1622_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 6, v___x_1636_);
v___x_1638_ = v___x_1634_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_leanOptions_1616_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_moreLeanArgs_1617_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_weakLeanArgs_1618_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_moreLeancArgs_1619_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_moreServerOptions_1620_);
lean_ctor_set(v_reuseFailAlloc_1639_, 5, v_weakLeancArgs_1621_);
lean_ctor_set(v_reuseFailAlloc_1639_, 6, v___x_1636_);
lean_ctor_set(v_reuseFailAlloc_1639_, 7, v_moreLinkLibs_1623_);
lean_ctor_set(v_reuseFailAlloc_1639_, 8, v_moreLinkArgs_1624_);
lean_ctor_set(v_reuseFailAlloc_1639_, 9, v_weakLinkArgs_1625_);
lean_ctor_set(v_reuseFailAlloc_1639_, 10, v_platformIndependent_1627_);
lean_ctor_set(v_reuseFailAlloc_1639_, 11, v_dynlibs_1629_);
lean_ctor_set(v_reuseFailAlloc_1639_, 12, v_plugins_1630_);
lean_ctor_set_uint8(v_reuseFailAlloc_1639_, sizeof(void*)*13, v_buildType_1615_);
lean_ctor_set_uint8(v_reuseFailAlloc_1639_, sizeof(void*)*13 + 1, v_backend_1626_);
lean_ctor_set_uint8(v_reuseFailAlloc_1639_, sizeof(void*)*13 + 2, v_precompileImports_1628_);
lean_ctor_set_uint8(v_reuseFailAlloc_1639_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1631_);
lean_ctor_set_uint8(v_reuseFailAlloc_1639_, sizeof(void*)*13 + 4, v_allowNonModules_1632_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1645_);
lean_dec_ref(v_x_1645_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1658_){
_start:
{
lean_object* v_moreLinkLibs_1659_; 
v_moreLinkLibs_1659_ = lean_ctor_get(v_cfg_1658_, 7);
lean_inc_ref(v_moreLinkLibs_1659_);
return v_moreLinkLibs_1659_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1660_);
lean_dec_ref(v_cfg_1660_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1662_, lean_object* v_cfg_1663_){
_start:
{
uint8_t v_buildType_1664_; lean_object* v_leanOptions_1665_; lean_object* v_moreLeanArgs_1666_; lean_object* v_weakLeanArgs_1667_; lean_object* v_moreLeancArgs_1668_; lean_object* v_moreServerOptions_1669_; lean_object* v_weakLeancArgs_1670_; lean_object* v_moreLinkObjs_1671_; lean_object* v_moreLinkArgs_1672_; lean_object* v_weakLinkArgs_1673_; uint8_t v_backend_1674_; lean_object* v_platformIndependent_1675_; uint8_t v_precompileImports_1676_; lean_object* v_dynlibs_1677_; lean_object* v_plugins_1678_; uint8_t v_requiresModuleSystem_1679_; uint8_t v_allowNonModules_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
v_buildType_1664_ = lean_ctor_get_uint8(v_cfg_1663_, sizeof(void*)*13);
v_leanOptions_1665_ = lean_ctor_get(v_cfg_1663_, 0);
v_moreLeanArgs_1666_ = lean_ctor_get(v_cfg_1663_, 1);
v_weakLeanArgs_1667_ = lean_ctor_get(v_cfg_1663_, 2);
v_moreLeancArgs_1668_ = lean_ctor_get(v_cfg_1663_, 3);
v_moreServerOptions_1669_ = lean_ctor_get(v_cfg_1663_, 4);
v_weakLeancArgs_1670_ = lean_ctor_get(v_cfg_1663_, 5);
v_moreLinkObjs_1671_ = lean_ctor_get(v_cfg_1663_, 6);
v_moreLinkArgs_1672_ = lean_ctor_get(v_cfg_1663_, 8);
v_weakLinkArgs_1673_ = lean_ctor_get(v_cfg_1663_, 9);
v_backend_1674_ = lean_ctor_get_uint8(v_cfg_1663_, sizeof(void*)*13 + 1);
v_platformIndependent_1675_ = lean_ctor_get(v_cfg_1663_, 10);
v_precompileImports_1676_ = lean_ctor_get_uint8(v_cfg_1663_, sizeof(void*)*13 + 2);
v_dynlibs_1677_ = lean_ctor_get(v_cfg_1663_, 11);
v_plugins_1678_ = lean_ctor_get(v_cfg_1663_, 12);
v_requiresModuleSystem_1679_ = lean_ctor_get_uint8(v_cfg_1663_, sizeof(void*)*13 + 3);
v_allowNonModules_1680_ = lean_ctor_get_uint8(v_cfg_1663_, sizeof(void*)*13 + 4);
v_isSharedCheck_1687_ = !lean_is_exclusive(v_cfg_1663_);
if (v_isSharedCheck_1687_ == 0)
{
lean_object* v_unused_1688_; 
v_unused_1688_ = lean_ctor_get(v_cfg_1663_, 7);
lean_dec(v_unused_1688_);
v___x_1682_ = v_cfg_1663_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_plugins_1678_);
lean_inc(v_dynlibs_1677_);
lean_inc(v_platformIndependent_1675_);
lean_inc(v_weakLinkArgs_1673_);
lean_inc(v_moreLinkArgs_1672_);
lean_inc(v_moreLinkObjs_1671_);
lean_inc(v_weakLeancArgs_1670_);
lean_inc(v_moreServerOptions_1669_);
lean_inc(v_moreLeancArgs_1668_);
lean_inc(v_weakLeanArgs_1667_);
lean_inc(v_moreLeanArgs_1666_);
lean_inc(v_leanOptions_1665_);
lean_dec(v_cfg_1663_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 7, v_val_1662_);
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_leanOptions_1665_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_moreLeanArgs_1666_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_weakLeanArgs_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_moreLeancArgs_1668_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_moreServerOptions_1669_);
lean_ctor_set(v_reuseFailAlloc_1686_, 5, v_weakLeancArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1686_, 6, v_moreLinkObjs_1671_);
lean_ctor_set(v_reuseFailAlloc_1686_, 7, v_val_1662_);
lean_ctor_set(v_reuseFailAlloc_1686_, 8, v_moreLinkArgs_1672_);
lean_ctor_set(v_reuseFailAlloc_1686_, 9, v_weakLinkArgs_1673_);
lean_ctor_set(v_reuseFailAlloc_1686_, 10, v_platformIndependent_1675_);
lean_ctor_set(v_reuseFailAlloc_1686_, 11, v_dynlibs_1677_);
lean_ctor_set(v_reuseFailAlloc_1686_, 12, v_plugins_1678_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*13, v_buildType_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*13 + 1, v_backend_1674_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*13 + 2, v_precompileImports_1676_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1679_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*13 + 4, v_allowNonModules_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1689_, lean_object* v_cfg_1690_){
_start:
{
uint8_t v_buildType_1691_; lean_object* v_leanOptions_1692_; lean_object* v_moreLeanArgs_1693_; lean_object* v_weakLeanArgs_1694_; lean_object* v_moreLeancArgs_1695_; lean_object* v_moreServerOptions_1696_; lean_object* v_weakLeancArgs_1697_; lean_object* v_moreLinkObjs_1698_; lean_object* v_moreLinkLibs_1699_; lean_object* v_moreLinkArgs_1700_; lean_object* v_weakLinkArgs_1701_; uint8_t v_backend_1702_; lean_object* v_platformIndependent_1703_; uint8_t v_precompileImports_1704_; lean_object* v_dynlibs_1705_; lean_object* v_plugins_1706_; uint8_t v_requiresModuleSystem_1707_; uint8_t v_allowNonModules_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1716_; 
v_buildType_1691_ = lean_ctor_get_uint8(v_cfg_1690_, sizeof(void*)*13);
v_leanOptions_1692_ = lean_ctor_get(v_cfg_1690_, 0);
v_moreLeanArgs_1693_ = lean_ctor_get(v_cfg_1690_, 1);
v_weakLeanArgs_1694_ = lean_ctor_get(v_cfg_1690_, 2);
v_moreLeancArgs_1695_ = lean_ctor_get(v_cfg_1690_, 3);
v_moreServerOptions_1696_ = lean_ctor_get(v_cfg_1690_, 4);
v_weakLeancArgs_1697_ = lean_ctor_get(v_cfg_1690_, 5);
v_moreLinkObjs_1698_ = lean_ctor_get(v_cfg_1690_, 6);
v_moreLinkLibs_1699_ = lean_ctor_get(v_cfg_1690_, 7);
v_moreLinkArgs_1700_ = lean_ctor_get(v_cfg_1690_, 8);
v_weakLinkArgs_1701_ = lean_ctor_get(v_cfg_1690_, 9);
v_backend_1702_ = lean_ctor_get_uint8(v_cfg_1690_, sizeof(void*)*13 + 1);
v_platformIndependent_1703_ = lean_ctor_get(v_cfg_1690_, 10);
v_precompileImports_1704_ = lean_ctor_get_uint8(v_cfg_1690_, sizeof(void*)*13 + 2);
v_dynlibs_1705_ = lean_ctor_get(v_cfg_1690_, 11);
v_plugins_1706_ = lean_ctor_get(v_cfg_1690_, 12);
v_requiresModuleSystem_1707_ = lean_ctor_get_uint8(v_cfg_1690_, sizeof(void*)*13 + 3);
v_allowNonModules_1708_ = lean_ctor_get_uint8(v_cfg_1690_, sizeof(void*)*13 + 4);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_cfg_1690_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1710_ = v_cfg_1690_;
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_plugins_1706_);
lean_inc(v_dynlibs_1705_);
lean_inc(v_platformIndependent_1703_);
lean_inc(v_weakLinkArgs_1701_);
lean_inc(v_moreLinkArgs_1700_);
lean_inc(v_moreLinkLibs_1699_);
lean_inc(v_moreLinkObjs_1698_);
lean_inc(v_weakLeancArgs_1697_);
lean_inc(v_moreServerOptions_1696_);
lean_inc(v_moreLeancArgs_1695_);
lean_inc(v_weakLeanArgs_1694_);
lean_inc(v_moreLeanArgs_1693_);
lean_inc(v_leanOptions_1692_);
lean_dec(v_cfg_1690_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1716_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1712_ = lean_apply_1(v_f_1689_, v_moreLinkLibs_1699_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 7, v___x_1712_);
v___x_1714_ = v___x_1710_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_leanOptions_1692_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_moreLeanArgs_1693_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_weakLeanArgs_1694_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_moreLeancArgs_1695_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v_moreServerOptions_1696_);
lean_ctor_set(v_reuseFailAlloc_1715_, 5, v_weakLeancArgs_1697_);
lean_ctor_set(v_reuseFailAlloc_1715_, 6, v_moreLinkObjs_1698_);
lean_ctor_set(v_reuseFailAlloc_1715_, 7, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1715_, 8, v_moreLinkArgs_1700_);
lean_ctor_set(v_reuseFailAlloc_1715_, 9, v_weakLinkArgs_1701_);
lean_ctor_set(v_reuseFailAlloc_1715_, 10, v_platformIndependent_1703_);
lean_ctor_set(v_reuseFailAlloc_1715_, 11, v_dynlibs_1705_);
lean_ctor_set(v_reuseFailAlloc_1715_, 12, v_plugins_1706_);
lean_ctor_set_uint8(v_reuseFailAlloc_1715_, sizeof(void*)*13, v_buildType_1691_);
lean_ctor_set_uint8(v_reuseFailAlloc_1715_, sizeof(void*)*13 + 1, v_backend_1702_);
lean_ctor_set_uint8(v_reuseFailAlloc_1715_, sizeof(void*)*13 + 2, v_precompileImports_1704_);
lean_ctor_set_uint8(v_reuseFailAlloc_1715_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1707_);
lean_ctor_set_uint8(v_reuseFailAlloc_1715_, sizeof(void*)*13 + 4, v_allowNonModules_1708_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1727_){
_start:
{
lean_object* v_moreLinkArgs_1728_; 
v_moreLinkArgs_1728_ = lean_ctor_get(v_cfg_1727_, 8);
lean_inc_ref(v_moreLinkArgs_1728_);
return v_moreLinkArgs_1728_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1729_);
lean_dec_ref(v_cfg_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1731_, lean_object* v_cfg_1732_){
_start:
{
uint8_t v_buildType_1733_; lean_object* v_leanOptions_1734_; lean_object* v_moreLeanArgs_1735_; lean_object* v_weakLeanArgs_1736_; lean_object* v_moreLeancArgs_1737_; lean_object* v_moreServerOptions_1738_; lean_object* v_weakLeancArgs_1739_; lean_object* v_moreLinkObjs_1740_; lean_object* v_moreLinkLibs_1741_; lean_object* v_weakLinkArgs_1742_; uint8_t v_backend_1743_; lean_object* v_platformIndependent_1744_; uint8_t v_precompileImports_1745_; lean_object* v_dynlibs_1746_; lean_object* v_plugins_1747_; uint8_t v_requiresModuleSystem_1748_; uint8_t v_allowNonModules_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
v_buildType_1733_ = lean_ctor_get_uint8(v_cfg_1732_, sizeof(void*)*13);
v_leanOptions_1734_ = lean_ctor_get(v_cfg_1732_, 0);
v_moreLeanArgs_1735_ = lean_ctor_get(v_cfg_1732_, 1);
v_weakLeanArgs_1736_ = lean_ctor_get(v_cfg_1732_, 2);
v_moreLeancArgs_1737_ = lean_ctor_get(v_cfg_1732_, 3);
v_moreServerOptions_1738_ = lean_ctor_get(v_cfg_1732_, 4);
v_weakLeancArgs_1739_ = lean_ctor_get(v_cfg_1732_, 5);
v_moreLinkObjs_1740_ = lean_ctor_get(v_cfg_1732_, 6);
v_moreLinkLibs_1741_ = lean_ctor_get(v_cfg_1732_, 7);
v_weakLinkArgs_1742_ = lean_ctor_get(v_cfg_1732_, 9);
v_backend_1743_ = lean_ctor_get_uint8(v_cfg_1732_, sizeof(void*)*13 + 1);
v_platformIndependent_1744_ = lean_ctor_get(v_cfg_1732_, 10);
v_precompileImports_1745_ = lean_ctor_get_uint8(v_cfg_1732_, sizeof(void*)*13 + 2);
v_dynlibs_1746_ = lean_ctor_get(v_cfg_1732_, 11);
v_plugins_1747_ = lean_ctor_get(v_cfg_1732_, 12);
v_requiresModuleSystem_1748_ = lean_ctor_get_uint8(v_cfg_1732_, sizeof(void*)*13 + 3);
v_allowNonModules_1749_ = lean_ctor_get_uint8(v_cfg_1732_, sizeof(void*)*13 + 4);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_cfg_1732_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v_cfg_1732_, 8);
lean_dec(v_unused_1757_);
v___x_1751_ = v_cfg_1732_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_plugins_1747_);
lean_inc(v_dynlibs_1746_);
lean_inc(v_platformIndependent_1744_);
lean_inc(v_weakLinkArgs_1742_);
lean_inc(v_moreLinkLibs_1741_);
lean_inc(v_moreLinkObjs_1740_);
lean_inc(v_weakLeancArgs_1739_);
lean_inc(v_moreServerOptions_1738_);
lean_inc(v_moreLeancArgs_1737_);
lean_inc(v_weakLeanArgs_1736_);
lean_inc(v_moreLeanArgs_1735_);
lean_inc(v_leanOptions_1734_);
lean_dec(v_cfg_1732_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 8, v_val_1731_);
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_leanOptions_1734_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_moreLeanArgs_1735_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_weakLeanArgs_1736_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_moreLeancArgs_1737_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_moreServerOptions_1738_);
lean_ctor_set(v_reuseFailAlloc_1755_, 5, v_weakLeancArgs_1739_);
lean_ctor_set(v_reuseFailAlloc_1755_, 6, v_moreLinkObjs_1740_);
lean_ctor_set(v_reuseFailAlloc_1755_, 7, v_moreLinkLibs_1741_);
lean_ctor_set(v_reuseFailAlloc_1755_, 8, v_val_1731_);
lean_ctor_set(v_reuseFailAlloc_1755_, 9, v_weakLinkArgs_1742_);
lean_ctor_set(v_reuseFailAlloc_1755_, 10, v_platformIndependent_1744_);
lean_ctor_set(v_reuseFailAlloc_1755_, 11, v_dynlibs_1746_);
lean_ctor_set(v_reuseFailAlloc_1755_, 12, v_plugins_1747_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*13, v_buildType_1733_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*13 + 1, v_backend_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*13 + 2, v_precompileImports_1745_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1755_, sizeof(void*)*13 + 4, v_allowNonModules_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1758_, lean_object* v_cfg_1759_){
_start:
{
uint8_t v_buildType_1760_; lean_object* v_leanOptions_1761_; lean_object* v_moreLeanArgs_1762_; lean_object* v_weakLeanArgs_1763_; lean_object* v_moreLeancArgs_1764_; lean_object* v_moreServerOptions_1765_; lean_object* v_weakLeancArgs_1766_; lean_object* v_moreLinkObjs_1767_; lean_object* v_moreLinkLibs_1768_; lean_object* v_moreLinkArgs_1769_; lean_object* v_weakLinkArgs_1770_; uint8_t v_backend_1771_; lean_object* v_platformIndependent_1772_; uint8_t v_precompileImports_1773_; lean_object* v_dynlibs_1774_; lean_object* v_plugins_1775_; uint8_t v_requiresModuleSystem_1776_; uint8_t v_allowNonModules_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1785_; 
v_buildType_1760_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*13);
v_leanOptions_1761_ = lean_ctor_get(v_cfg_1759_, 0);
v_moreLeanArgs_1762_ = lean_ctor_get(v_cfg_1759_, 1);
v_weakLeanArgs_1763_ = lean_ctor_get(v_cfg_1759_, 2);
v_moreLeancArgs_1764_ = lean_ctor_get(v_cfg_1759_, 3);
v_moreServerOptions_1765_ = lean_ctor_get(v_cfg_1759_, 4);
v_weakLeancArgs_1766_ = lean_ctor_get(v_cfg_1759_, 5);
v_moreLinkObjs_1767_ = lean_ctor_get(v_cfg_1759_, 6);
v_moreLinkLibs_1768_ = lean_ctor_get(v_cfg_1759_, 7);
v_moreLinkArgs_1769_ = lean_ctor_get(v_cfg_1759_, 8);
v_weakLinkArgs_1770_ = lean_ctor_get(v_cfg_1759_, 9);
v_backend_1771_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*13 + 1);
v_platformIndependent_1772_ = lean_ctor_get(v_cfg_1759_, 10);
v_precompileImports_1773_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*13 + 2);
v_dynlibs_1774_ = lean_ctor_get(v_cfg_1759_, 11);
v_plugins_1775_ = lean_ctor_get(v_cfg_1759_, 12);
v_requiresModuleSystem_1776_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*13 + 3);
v_allowNonModules_1777_ = lean_ctor_get_uint8(v_cfg_1759_, sizeof(void*)*13 + 4);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_cfg_1759_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1779_ = v_cfg_1759_;
v_isShared_1780_ = v_isSharedCheck_1785_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_plugins_1775_);
lean_inc(v_dynlibs_1774_);
lean_inc(v_platformIndependent_1772_);
lean_inc(v_weakLinkArgs_1770_);
lean_inc(v_moreLinkArgs_1769_);
lean_inc(v_moreLinkLibs_1768_);
lean_inc(v_moreLinkObjs_1767_);
lean_inc(v_weakLeancArgs_1766_);
lean_inc(v_moreServerOptions_1765_);
lean_inc(v_moreLeancArgs_1764_);
lean_inc(v_weakLeanArgs_1763_);
lean_inc(v_moreLeanArgs_1762_);
lean_inc(v_leanOptions_1761_);
lean_dec(v_cfg_1759_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1785_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1781_; lean_object* v___x_1783_; 
v___x_1781_ = lean_apply_1(v_f_1758_, v_moreLinkArgs_1769_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 8, v___x_1781_);
v___x_1783_ = v___x_1779_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_leanOptions_1761_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_moreLeanArgs_1762_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_weakLeanArgs_1763_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_moreLeancArgs_1764_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_moreServerOptions_1765_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v_weakLeancArgs_1766_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_moreLinkObjs_1767_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v_moreLinkLibs_1768_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1784_, 9, v_weakLinkArgs_1770_);
lean_ctor_set(v_reuseFailAlloc_1784_, 10, v_platformIndependent_1772_);
lean_ctor_set(v_reuseFailAlloc_1784_, 11, v_dynlibs_1774_);
lean_ctor_set(v_reuseFailAlloc_1784_, 12, v_plugins_1775_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*13, v_buildType_1760_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*13 + 1, v_backend_1771_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*13 + 2, v_precompileImports_1773_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1776_);
lean_ctor_set_uint8(v_reuseFailAlloc_1784_, sizeof(void*)*13 + 4, v_allowNonModules_1777_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1796_){
_start:
{
lean_object* v_weakLinkArgs_1797_; 
v_weakLinkArgs_1797_ = lean_ctor_get(v_cfg_1796_, 9);
lean_inc_ref(v_weakLinkArgs_1797_);
return v_weakLinkArgs_1797_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1798_);
lean_dec_ref(v_cfg_1798_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1800_, lean_object* v_cfg_1801_){
_start:
{
uint8_t v_buildType_1802_; lean_object* v_leanOptions_1803_; lean_object* v_moreLeanArgs_1804_; lean_object* v_weakLeanArgs_1805_; lean_object* v_moreLeancArgs_1806_; lean_object* v_moreServerOptions_1807_; lean_object* v_weakLeancArgs_1808_; lean_object* v_moreLinkObjs_1809_; lean_object* v_moreLinkLibs_1810_; lean_object* v_moreLinkArgs_1811_; uint8_t v_backend_1812_; lean_object* v_platformIndependent_1813_; uint8_t v_precompileImports_1814_; lean_object* v_dynlibs_1815_; lean_object* v_plugins_1816_; uint8_t v_requiresModuleSystem_1817_; uint8_t v_allowNonModules_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_buildType_1802_ = lean_ctor_get_uint8(v_cfg_1801_, sizeof(void*)*13);
v_leanOptions_1803_ = lean_ctor_get(v_cfg_1801_, 0);
v_moreLeanArgs_1804_ = lean_ctor_get(v_cfg_1801_, 1);
v_weakLeanArgs_1805_ = lean_ctor_get(v_cfg_1801_, 2);
v_moreLeancArgs_1806_ = lean_ctor_get(v_cfg_1801_, 3);
v_moreServerOptions_1807_ = lean_ctor_get(v_cfg_1801_, 4);
v_weakLeancArgs_1808_ = lean_ctor_get(v_cfg_1801_, 5);
v_moreLinkObjs_1809_ = lean_ctor_get(v_cfg_1801_, 6);
v_moreLinkLibs_1810_ = lean_ctor_get(v_cfg_1801_, 7);
v_moreLinkArgs_1811_ = lean_ctor_get(v_cfg_1801_, 8);
v_backend_1812_ = lean_ctor_get_uint8(v_cfg_1801_, sizeof(void*)*13 + 1);
v_platformIndependent_1813_ = lean_ctor_get(v_cfg_1801_, 10);
v_precompileImports_1814_ = lean_ctor_get_uint8(v_cfg_1801_, sizeof(void*)*13 + 2);
v_dynlibs_1815_ = lean_ctor_get(v_cfg_1801_, 11);
v_plugins_1816_ = lean_ctor_get(v_cfg_1801_, 12);
v_requiresModuleSystem_1817_ = lean_ctor_get_uint8(v_cfg_1801_, sizeof(void*)*13 + 3);
v_allowNonModules_1818_ = lean_ctor_get_uint8(v_cfg_1801_, sizeof(void*)*13 + 4);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_cfg_1801_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v_cfg_1801_, 9);
lean_dec(v_unused_1826_);
v___x_1820_ = v_cfg_1801_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_plugins_1816_);
lean_inc(v_dynlibs_1815_);
lean_inc(v_platformIndependent_1813_);
lean_inc(v_moreLinkArgs_1811_);
lean_inc(v_moreLinkLibs_1810_);
lean_inc(v_moreLinkObjs_1809_);
lean_inc(v_weakLeancArgs_1808_);
lean_inc(v_moreServerOptions_1807_);
lean_inc(v_moreLeancArgs_1806_);
lean_inc(v_weakLeanArgs_1805_);
lean_inc(v_moreLeanArgs_1804_);
lean_inc(v_leanOptions_1803_);
lean_dec(v_cfg_1801_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 9, v_val_1800_);
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_leanOptions_1803_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_moreLeanArgs_1804_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_weakLeanArgs_1805_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_moreLeancArgs_1806_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v_moreServerOptions_1807_);
lean_ctor_set(v_reuseFailAlloc_1824_, 5, v_weakLeancArgs_1808_);
lean_ctor_set(v_reuseFailAlloc_1824_, 6, v_moreLinkObjs_1809_);
lean_ctor_set(v_reuseFailAlloc_1824_, 7, v_moreLinkLibs_1810_);
lean_ctor_set(v_reuseFailAlloc_1824_, 8, v_moreLinkArgs_1811_);
lean_ctor_set(v_reuseFailAlloc_1824_, 9, v_val_1800_);
lean_ctor_set(v_reuseFailAlloc_1824_, 10, v_platformIndependent_1813_);
lean_ctor_set(v_reuseFailAlloc_1824_, 11, v_dynlibs_1815_);
lean_ctor_set(v_reuseFailAlloc_1824_, 12, v_plugins_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13, v_buildType_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 1, v_backend_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 2, v_precompileImports_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*13 + 4, v_allowNonModules_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1827_, lean_object* v_cfg_1828_){
_start:
{
uint8_t v_buildType_1829_; lean_object* v_leanOptions_1830_; lean_object* v_moreLeanArgs_1831_; lean_object* v_weakLeanArgs_1832_; lean_object* v_moreLeancArgs_1833_; lean_object* v_moreServerOptions_1834_; lean_object* v_weakLeancArgs_1835_; lean_object* v_moreLinkObjs_1836_; lean_object* v_moreLinkLibs_1837_; lean_object* v_moreLinkArgs_1838_; lean_object* v_weakLinkArgs_1839_; uint8_t v_backend_1840_; lean_object* v_platformIndependent_1841_; uint8_t v_precompileImports_1842_; lean_object* v_dynlibs_1843_; lean_object* v_plugins_1844_; uint8_t v_requiresModuleSystem_1845_; uint8_t v_allowNonModules_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v_buildType_1829_ = lean_ctor_get_uint8(v_cfg_1828_, sizeof(void*)*13);
v_leanOptions_1830_ = lean_ctor_get(v_cfg_1828_, 0);
v_moreLeanArgs_1831_ = lean_ctor_get(v_cfg_1828_, 1);
v_weakLeanArgs_1832_ = lean_ctor_get(v_cfg_1828_, 2);
v_moreLeancArgs_1833_ = lean_ctor_get(v_cfg_1828_, 3);
v_moreServerOptions_1834_ = lean_ctor_get(v_cfg_1828_, 4);
v_weakLeancArgs_1835_ = lean_ctor_get(v_cfg_1828_, 5);
v_moreLinkObjs_1836_ = lean_ctor_get(v_cfg_1828_, 6);
v_moreLinkLibs_1837_ = lean_ctor_get(v_cfg_1828_, 7);
v_moreLinkArgs_1838_ = lean_ctor_get(v_cfg_1828_, 8);
v_weakLinkArgs_1839_ = lean_ctor_get(v_cfg_1828_, 9);
v_backend_1840_ = lean_ctor_get_uint8(v_cfg_1828_, sizeof(void*)*13 + 1);
v_platformIndependent_1841_ = lean_ctor_get(v_cfg_1828_, 10);
v_precompileImports_1842_ = lean_ctor_get_uint8(v_cfg_1828_, sizeof(void*)*13 + 2);
v_dynlibs_1843_ = lean_ctor_get(v_cfg_1828_, 11);
v_plugins_1844_ = lean_ctor_get(v_cfg_1828_, 12);
v_requiresModuleSystem_1845_ = lean_ctor_get_uint8(v_cfg_1828_, sizeof(void*)*13 + 3);
v_allowNonModules_1846_ = lean_ctor_get_uint8(v_cfg_1828_, sizeof(void*)*13 + 4);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_cfg_1828_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1848_ = v_cfg_1828_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_plugins_1844_);
lean_inc(v_dynlibs_1843_);
lean_inc(v_platformIndependent_1841_);
lean_inc(v_weakLinkArgs_1839_);
lean_inc(v_moreLinkArgs_1838_);
lean_inc(v_moreLinkLibs_1837_);
lean_inc(v_moreLinkObjs_1836_);
lean_inc(v_weakLeancArgs_1835_);
lean_inc(v_moreServerOptions_1834_);
lean_inc(v_moreLeancArgs_1833_);
lean_inc(v_weakLeanArgs_1832_);
lean_inc(v_moreLeanArgs_1831_);
lean_inc(v_leanOptions_1830_);
lean_dec(v_cfg_1828_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_apply_1(v_f_1827_, v_weakLinkArgs_1839_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 9, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_leanOptions_1830_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_moreLeanArgs_1831_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_weakLeanArgs_1832_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_moreLeancArgs_1833_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_moreServerOptions_1834_);
lean_ctor_set(v_reuseFailAlloc_1853_, 5, v_weakLeancArgs_1835_);
lean_ctor_set(v_reuseFailAlloc_1853_, 6, v_moreLinkObjs_1836_);
lean_ctor_set(v_reuseFailAlloc_1853_, 7, v_moreLinkLibs_1837_);
lean_ctor_set(v_reuseFailAlloc_1853_, 8, v_moreLinkArgs_1838_);
lean_ctor_set(v_reuseFailAlloc_1853_, 9, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1853_, 10, v_platformIndependent_1841_);
lean_ctor_set(v_reuseFailAlloc_1853_, 11, v_dynlibs_1843_);
lean_ctor_set(v_reuseFailAlloc_1853_, 12, v_plugins_1844_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*13, v_buildType_1829_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*13 + 1, v_backend_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*13 + 2, v_precompileImports_1842_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1845_);
lean_ctor_set_uint8(v_reuseFailAlloc_1853_, sizeof(void*)*13 + 4, v_allowNonModules_1846_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1865_){
_start:
{
uint8_t v_backend_1866_; 
v_backend_1866_ = lean_ctor_get_uint8(v_cfg_1865_, sizeof(void*)*13 + 1);
return v_backend_1866_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1867_){
_start:
{
uint8_t v_res_1868_; lean_object* v_r_1869_; 
v_res_1868_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1867_);
lean_dec_ref(v_cfg_1867_);
v_r_1869_ = lean_box(v_res_1868_);
return v_r_1869_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1870_, lean_object* v_cfg_1871_){
_start:
{
uint8_t v_buildType_1872_; lean_object* v_leanOptions_1873_; lean_object* v_moreLeanArgs_1874_; lean_object* v_weakLeanArgs_1875_; lean_object* v_moreLeancArgs_1876_; lean_object* v_moreServerOptions_1877_; lean_object* v_weakLeancArgs_1878_; lean_object* v_moreLinkObjs_1879_; lean_object* v_moreLinkLibs_1880_; lean_object* v_moreLinkArgs_1881_; lean_object* v_weakLinkArgs_1882_; lean_object* v_platformIndependent_1883_; uint8_t v_precompileImports_1884_; lean_object* v_dynlibs_1885_; lean_object* v_plugins_1886_; uint8_t v_requiresModuleSystem_1887_; uint8_t v_allowNonModules_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
v_buildType_1872_ = lean_ctor_get_uint8(v_cfg_1871_, sizeof(void*)*13);
v_leanOptions_1873_ = lean_ctor_get(v_cfg_1871_, 0);
v_moreLeanArgs_1874_ = lean_ctor_get(v_cfg_1871_, 1);
v_weakLeanArgs_1875_ = lean_ctor_get(v_cfg_1871_, 2);
v_moreLeancArgs_1876_ = lean_ctor_get(v_cfg_1871_, 3);
v_moreServerOptions_1877_ = lean_ctor_get(v_cfg_1871_, 4);
v_weakLeancArgs_1878_ = lean_ctor_get(v_cfg_1871_, 5);
v_moreLinkObjs_1879_ = lean_ctor_get(v_cfg_1871_, 6);
v_moreLinkLibs_1880_ = lean_ctor_get(v_cfg_1871_, 7);
v_moreLinkArgs_1881_ = lean_ctor_get(v_cfg_1871_, 8);
v_weakLinkArgs_1882_ = lean_ctor_get(v_cfg_1871_, 9);
v_platformIndependent_1883_ = lean_ctor_get(v_cfg_1871_, 10);
v_precompileImports_1884_ = lean_ctor_get_uint8(v_cfg_1871_, sizeof(void*)*13 + 2);
v_dynlibs_1885_ = lean_ctor_get(v_cfg_1871_, 11);
v_plugins_1886_ = lean_ctor_get(v_cfg_1871_, 12);
v_requiresModuleSystem_1887_ = lean_ctor_get_uint8(v_cfg_1871_, sizeof(void*)*13 + 3);
v_allowNonModules_1888_ = lean_ctor_get_uint8(v_cfg_1871_, sizeof(void*)*13 + 4);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_cfg_1871_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v_cfg_1871_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_plugins_1886_);
lean_inc(v_dynlibs_1885_);
lean_inc(v_platformIndependent_1883_);
lean_inc(v_weakLinkArgs_1882_);
lean_inc(v_moreLinkArgs_1881_);
lean_inc(v_moreLinkLibs_1880_);
lean_inc(v_moreLinkObjs_1879_);
lean_inc(v_weakLeancArgs_1878_);
lean_inc(v_moreServerOptions_1877_);
lean_inc(v_moreLeancArgs_1876_);
lean_inc(v_weakLeanArgs_1875_);
lean_inc(v_moreLeanArgs_1874_);
lean_inc(v_leanOptions_1873_);
lean_dec(v_cfg_1871_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_leanOptions_1873_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_moreLeanArgs_1874_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_weakLeanArgs_1875_);
lean_ctor_set(v_reuseFailAlloc_1894_, 3, v_moreLeancArgs_1876_);
lean_ctor_set(v_reuseFailAlloc_1894_, 4, v_moreServerOptions_1877_);
lean_ctor_set(v_reuseFailAlloc_1894_, 5, v_weakLeancArgs_1878_);
lean_ctor_set(v_reuseFailAlloc_1894_, 6, v_moreLinkObjs_1879_);
lean_ctor_set(v_reuseFailAlloc_1894_, 7, v_moreLinkLibs_1880_);
lean_ctor_set(v_reuseFailAlloc_1894_, 8, v_moreLinkArgs_1881_);
lean_ctor_set(v_reuseFailAlloc_1894_, 9, v_weakLinkArgs_1882_);
lean_ctor_set(v_reuseFailAlloc_1894_, 10, v_platformIndependent_1883_);
lean_ctor_set(v_reuseFailAlloc_1894_, 11, v_dynlibs_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 12, v_plugins_1886_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*13, v_buildType_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*13 + 2, v_precompileImports_1884_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1887_);
lean_ctor_set_uint8(v_reuseFailAlloc_1894_, sizeof(void*)*13 + 4, v_allowNonModules_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
lean_ctor_set_uint8(v___x_1893_, sizeof(void*)*13 + 1, v_val_1870_);
return v___x_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1896_, lean_object* v_cfg_1897_){
_start:
{
uint8_t v_val_88__boxed_1898_; lean_object* v_res_1899_; 
v_val_88__boxed_1898_ = lean_unbox(v_val_1896_);
v_res_1899_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_88__boxed_1898_, v_cfg_1897_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1900_, lean_object* v_cfg_1901_){
_start:
{
uint8_t v_buildType_1902_; lean_object* v_leanOptions_1903_; lean_object* v_moreLeanArgs_1904_; lean_object* v_weakLeanArgs_1905_; lean_object* v_moreLeancArgs_1906_; lean_object* v_moreServerOptions_1907_; lean_object* v_weakLeancArgs_1908_; lean_object* v_moreLinkObjs_1909_; lean_object* v_moreLinkLibs_1910_; lean_object* v_moreLinkArgs_1911_; lean_object* v_weakLinkArgs_1912_; uint8_t v_backend_1913_; lean_object* v_platformIndependent_1914_; uint8_t v_precompileImports_1915_; lean_object* v_dynlibs_1916_; lean_object* v_plugins_1917_; uint8_t v_requiresModuleSystem_1918_; uint8_t v_allowNonModules_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1929_; 
v_buildType_1902_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*13);
v_leanOptions_1903_ = lean_ctor_get(v_cfg_1901_, 0);
v_moreLeanArgs_1904_ = lean_ctor_get(v_cfg_1901_, 1);
v_weakLeanArgs_1905_ = lean_ctor_get(v_cfg_1901_, 2);
v_moreLeancArgs_1906_ = lean_ctor_get(v_cfg_1901_, 3);
v_moreServerOptions_1907_ = lean_ctor_get(v_cfg_1901_, 4);
v_weakLeancArgs_1908_ = lean_ctor_get(v_cfg_1901_, 5);
v_moreLinkObjs_1909_ = lean_ctor_get(v_cfg_1901_, 6);
v_moreLinkLibs_1910_ = lean_ctor_get(v_cfg_1901_, 7);
v_moreLinkArgs_1911_ = lean_ctor_get(v_cfg_1901_, 8);
v_weakLinkArgs_1912_ = lean_ctor_get(v_cfg_1901_, 9);
v_backend_1913_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*13 + 1);
v_platformIndependent_1914_ = lean_ctor_get(v_cfg_1901_, 10);
v_precompileImports_1915_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*13 + 2);
v_dynlibs_1916_ = lean_ctor_get(v_cfg_1901_, 11);
v_plugins_1917_ = lean_ctor_get(v_cfg_1901_, 12);
v_requiresModuleSystem_1918_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*13 + 3);
v_allowNonModules_1919_ = lean_ctor_get_uint8(v_cfg_1901_, sizeof(void*)*13 + 4);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_cfg_1901_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1921_ = v_cfg_1901_;
v_isShared_1922_ = v_isSharedCheck_1929_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_plugins_1917_);
lean_inc(v_dynlibs_1916_);
lean_inc(v_platformIndependent_1914_);
lean_inc(v_weakLinkArgs_1912_);
lean_inc(v_moreLinkArgs_1911_);
lean_inc(v_moreLinkLibs_1910_);
lean_inc(v_moreLinkObjs_1909_);
lean_inc(v_weakLeancArgs_1908_);
lean_inc(v_moreServerOptions_1907_);
lean_inc(v_moreLeancArgs_1906_);
lean_inc(v_weakLeanArgs_1905_);
lean_inc(v_moreLeanArgs_1904_);
lean_inc(v_leanOptions_1903_);
lean_dec(v_cfg_1901_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1929_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = lean_box(v_backend_1913_);
v___x_1924_ = lean_apply_1(v_f_1900_, v___x_1923_);
if (v_isShared_1922_ == 0)
{
v___x_1926_ = v___x_1921_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_leanOptions_1903_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_moreLeanArgs_1904_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_weakLeanArgs_1905_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_moreLeancArgs_1906_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_moreServerOptions_1907_);
lean_ctor_set(v_reuseFailAlloc_1928_, 5, v_weakLeancArgs_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 6, v_moreLinkObjs_1909_);
lean_ctor_set(v_reuseFailAlloc_1928_, 7, v_moreLinkLibs_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 8, v_moreLinkArgs_1911_);
lean_ctor_set(v_reuseFailAlloc_1928_, 9, v_weakLinkArgs_1912_);
lean_ctor_set(v_reuseFailAlloc_1928_, 10, v_platformIndependent_1914_);
lean_ctor_set(v_reuseFailAlloc_1928_, 11, v_dynlibs_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 12, v_plugins_1917_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*13, v_buildType_1902_);
v___x_1926_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
uint8_t v___x_1927_; 
v___x_1927_ = lean_unbox(v___x_1924_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*13 + 1, v___x_1927_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*13 + 2, v_precompileImports_1915_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1918_);
lean_ctor_set_uint8(v___x_1926_, sizeof(void*)*13 + 4, v_allowNonModules_1919_);
return v___x_1926_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1930_){
_start:
{
uint8_t v___x_1931_; 
v___x_1931_ = 2;
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1932_){
_start:
{
uint8_t v_res_1933_; lean_object* v_r_1934_; 
v_res_1933_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1932_);
lean_dec_ref(v_x_1932_);
v_r_1934_ = lean_box(v_res_1933_);
return v_r_1934_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1946_){
_start:
{
lean_object* v_platformIndependent_1947_; 
v_platformIndependent_1947_ = lean_ctor_get(v_cfg_1946_, 10);
lean_inc(v_platformIndependent_1947_);
return v_platformIndependent_1947_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1948_);
lean_dec_ref(v_cfg_1948_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1950_, lean_object* v_cfg_1951_){
_start:
{
uint8_t v_buildType_1952_; lean_object* v_leanOptions_1953_; lean_object* v_moreLeanArgs_1954_; lean_object* v_weakLeanArgs_1955_; lean_object* v_moreLeancArgs_1956_; lean_object* v_moreServerOptions_1957_; lean_object* v_weakLeancArgs_1958_; lean_object* v_moreLinkObjs_1959_; lean_object* v_moreLinkLibs_1960_; lean_object* v_moreLinkArgs_1961_; lean_object* v_weakLinkArgs_1962_; uint8_t v_backend_1963_; uint8_t v_precompileImports_1964_; lean_object* v_dynlibs_1965_; lean_object* v_plugins_1966_; uint8_t v_requiresModuleSystem_1967_; uint8_t v_allowNonModules_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_buildType_1952_ = lean_ctor_get_uint8(v_cfg_1951_, sizeof(void*)*13);
v_leanOptions_1953_ = lean_ctor_get(v_cfg_1951_, 0);
v_moreLeanArgs_1954_ = lean_ctor_get(v_cfg_1951_, 1);
v_weakLeanArgs_1955_ = lean_ctor_get(v_cfg_1951_, 2);
v_moreLeancArgs_1956_ = lean_ctor_get(v_cfg_1951_, 3);
v_moreServerOptions_1957_ = lean_ctor_get(v_cfg_1951_, 4);
v_weakLeancArgs_1958_ = lean_ctor_get(v_cfg_1951_, 5);
v_moreLinkObjs_1959_ = lean_ctor_get(v_cfg_1951_, 6);
v_moreLinkLibs_1960_ = lean_ctor_get(v_cfg_1951_, 7);
v_moreLinkArgs_1961_ = lean_ctor_get(v_cfg_1951_, 8);
v_weakLinkArgs_1962_ = lean_ctor_get(v_cfg_1951_, 9);
v_backend_1963_ = lean_ctor_get_uint8(v_cfg_1951_, sizeof(void*)*13 + 1);
v_precompileImports_1964_ = lean_ctor_get_uint8(v_cfg_1951_, sizeof(void*)*13 + 2);
v_dynlibs_1965_ = lean_ctor_get(v_cfg_1951_, 11);
v_plugins_1966_ = lean_ctor_get(v_cfg_1951_, 12);
v_requiresModuleSystem_1967_ = lean_ctor_get_uint8(v_cfg_1951_, sizeof(void*)*13 + 3);
v_allowNonModules_1968_ = lean_ctor_get_uint8(v_cfg_1951_, sizeof(void*)*13 + 4);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_cfg_1951_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_cfg_1951_, 10);
lean_dec(v_unused_1976_);
v___x_1970_ = v_cfg_1951_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_plugins_1966_);
lean_inc(v_dynlibs_1965_);
lean_inc(v_weakLinkArgs_1962_);
lean_inc(v_moreLinkArgs_1961_);
lean_inc(v_moreLinkLibs_1960_);
lean_inc(v_moreLinkObjs_1959_);
lean_inc(v_weakLeancArgs_1958_);
lean_inc(v_moreServerOptions_1957_);
lean_inc(v_moreLeancArgs_1956_);
lean_inc(v_weakLeanArgs_1955_);
lean_inc(v_moreLeanArgs_1954_);
lean_inc(v_leanOptions_1953_);
lean_dec(v_cfg_1951_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 10, v_val_1950_);
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_leanOptions_1953_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v_moreLeanArgs_1954_);
lean_ctor_set(v_reuseFailAlloc_1974_, 2, v_weakLeanArgs_1955_);
lean_ctor_set(v_reuseFailAlloc_1974_, 3, v_moreLeancArgs_1956_);
lean_ctor_set(v_reuseFailAlloc_1974_, 4, v_moreServerOptions_1957_);
lean_ctor_set(v_reuseFailAlloc_1974_, 5, v_weakLeancArgs_1958_);
lean_ctor_set(v_reuseFailAlloc_1974_, 6, v_moreLinkObjs_1959_);
lean_ctor_set(v_reuseFailAlloc_1974_, 7, v_moreLinkLibs_1960_);
lean_ctor_set(v_reuseFailAlloc_1974_, 8, v_moreLinkArgs_1961_);
lean_ctor_set(v_reuseFailAlloc_1974_, 9, v_weakLinkArgs_1962_);
lean_ctor_set(v_reuseFailAlloc_1974_, 10, v_val_1950_);
lean_ctor_set(v_reuseFailAlloc_1974_, 11, v_dynlibs_1965_);
lean_ctor_set(v_reuseFailAlloc_1974_, 12, v_plugins_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1974_, sizeof(void*)*13, v_buildType_1952_);
lean_ctor_set_uint8(v_reuseFailAlloc_1974_, sizeof(void*)*13 + 1, v_backend_1963_);
lean_ctor_set_uint8(v_reuseFailAlloc_1974_, sizeof(void*)*13 + 2, v_precompileImports_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1974_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1974_, sizeof(void*)*13 + 4, v_allowNonModules_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_1977_, lean_object* v_cfg_1978_){
_start:
{
uint8_t v_buildType_1979_; lean_object* v_leanOptions_1980_; lean_object* v_moreLeanArgs_1981_; lean_object* v_weakLeanArgs_1982_; lean_object* v_moreLeancArgs_1983_; lean_object* v_moreServerOptions_1984_; lean_object* v_weakLeancArgs_1985_; lean_object* v_moreLinkObjs_1986_; lean_object* v_moreLinkLibs_1987_; lean_object* v_moreLinkArgs_1988_; lean_object* v_weakLinkArgs_1989_; uint8_t v_backend_1990_; lean_object* v_platformIndependent_1991_; uint8_t v_precompileImports_1992_; lean_object* v_dynlibs_1993_; lean_object* v_plugins_1994_; uint8_t v_requiresModuleSystem_1995_; uint8_t v_allowNonModules_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2004_; 
v_buildType_1979_ = lean_ctor_get_uint8(v_cfg_1978_, sizeof(void*)*13);
v_leanOptions_1980_ = lean_ctor_get(v_cfg_1978_, 0);
v_moreLeanArgs_1981_ = lean_ctor_get(v_cfg_1978_, 1);
v_weakLeanArgs_1982_ = lean_ctor_get(v_cfg_1978_, 2);
v_moreLeancArgs_1983_ = lean_ctor_get(v_cfg_1978_, 3);
v_moreServerOptions_1984_ = lean_ctor_get(v_cfg_1978_, 4);
v_weakLeancArgs_1985_ = lean_ctor_get(v_cfg_1978_, 5);
v_moreLinkObjs_1986_ = lean_ctor_get(v_cfg_1978_, 6);
v_moreLinkLibs_1987_ = lean_ctor_get(v_cfg_1978_, 7);
v_moreLinkArgs_1988_ = lean_ctor_get(v_cfg_1978_, 8);
v_weakLinkArgs_1989_ = lean_ctor_get(v_cfg_1978_, 9);
v_backend_1990_ = lean_ctor_get_uint8(v_cfg_1978_, sizeof(void*)*13 + 1);
v_platformIndependent_1991_ = lean_ctor_get(v_cfg_1978_, 10);
v_precompileImports_1992_ = lean_ctor_get_uint8(v_cfg_1978_, sizeof(void*)*13 + 2);
v_dynlibs_1993_ = lean_ctor_get(v_cfg_1978_, 11);
v_plugins_1994_ = lean_ctor_get(v_cfg_1978_, 12);
v_requiresModuleSystem_1995_ = lean_ctor_get_uint8(v_cfg_1978_, sizeof(void*)*13 + 3);
v_allowNonModules_1996_ = lean_ctor_get_uint8(v_cfg_1978_, sizeof(void*)*13 + 4);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_cfg_1978_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1998_ = v_cfg_1978_;
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_plugins_1994_);
lean_inc(v_dynlibs_1993_);
lean_inc(v_platformIndependent_1991_);
lean_inc(v_weakLinkArgs_1989_);
lean_inc(v_moreLinkArgs_1988_);
lean_inc(v_moreLinkLibs_1987_);
lean_inc(v_moreLinkObjs_1986_);
lean_inc(v_weakLeancArgs_1985_);
lean_inc(v_moreServerOptions_1984_);
lean_inc(v_moreLeancArgs_1983_);
lean_inc(v_weakLeanArgs_1982_);
lean_inc(v_moreLeanArgs_1981_);
lean_inc(v_leanOptions_1980_);
lean_dec(v_cfg_1978_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2004_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_apply_1(v_f_1977_, v_platformIndependent_1991_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 10, v___x_2000_);
v___x_2002_ = v___x_1998_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_leanOptions_1980_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_moreLeanArgs_1981_);
lean_ctor_set(v_reuseFailAlloc_2003_, 2, v_weakLeanArgs_1982_);
lean_ctor_set(v_reuseFailAlloc_2003_, 3, v_moreLeancArgs_1983_);
lean_ctor_set(v_reuseFailAlloc_2003_, 4, v_moreServerOptions_1984_);
lean_ctor_set(v_reuseFailAlloc_2003_, 5, v_weakLeancArgs_1985_);
lean_ctor_set(v_reuseFailAlloc_2003_, 6, v_moreLinkObjs_1986_);
lean_ctor_set(v_reuseFailAlloc_2003_, 7, v_moreLinkLibs_1987_);
lean_ctor_set(v_reuseFailAlloc_2003_, 8, v_moreLinkArgs_1988_);
lean_ctor_set(v_reuseFailAlloc_2003_, 9, v_weakLinkArgs_1989_);
lean_ctor_set(v_reuseFailAlloc_2003_, 10, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2003_, 11, v_dynlibs_1993_);
lean_ctor_set(v_reuseFailAlloc_2003_, 12, v_plugins_1994_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*13, v_buildType_1979_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*13 + 1, v_backend_1990_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*13 + 2, v_precompileImports_1992_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*13 + 3, v_requiresModuleSystem_1995_);
lean_ctor_set_uint8(v_reuseFailAlloc_2003_, sizeof(void*)*13 + 4, v_allowNonModules_1996_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_box(0);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_2007_);
lean_dec_ref(v_x_2007_);
return v_res_2008_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__0(lean_object* v_cfg_2020_){
_start:
{
uint8_t v_precompileImports_2021_; 
v_precompileImports_2021_ = lean_ctor_get_uint8(v_cfg_2020_, sizeof(void*)*13 + 2);
return v_precompileImports_2021_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__0___boxed(lean_object* v_cfg_2022_){
_start:
{
uint8_t v_res_2023_; lean_object* v_r_2024_; 
v_res_2023_ = l_Lake_LeanConfig_precompileImports___proj___lam__0(v_cfg_2022_);
lean_dec_ref(v_cfg_2022_);
v_r_2024_ = lean_box(v_res_2023_);
return v_r_2024_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1(uint8_t v_val_2025_, lean_object* v_cfg_2026_){
_start:
{
uint8_t v_buildType_2027_; lean_object* v_leanOptions_2028_; lean_object* v_moreLeanArgs_2029_; lean_object* v_weakLeanArgs_2030_; lean_object* v_moreLeancArgs_2031_; lean_object* v_moreServerOptions_2032_; lean_object* v_weakLeancArgs_2033_; lean_object* v_moreLinkObjs_2034_; lean_object* v_moreLinkLibs_2035_; lean_object* v_moreLinkArgs_2036_; lean_object* v_weakLinkArgs_2037_; uint8_t v_backend_2038_; lean_object* v_platformIndependent_2039_; lean_object* v_dynlibs_2040_; lean_object* v_plugins_2041_; uint8_t v_requiresModuleSystem_2042_; uint8_t v_allowNonModules_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
v_buildType_2027_ = lean_ctor_get_uint8(v_cfg_2026_, sizeof(void*)*13);
v_leanOptions_2028_ = lean_ctor_get(v_cfg_2026_, 0);
v_moreLeanArgs_2029_ = lean_ctor_get(v_cfg_2026_, 1);
v_weakLeanArgs_2030_ = lean_ctor_get(v_cfg_2026_, 2);
v_moreLeancArgs_2031_ = lean_ctor_get(v_cfg_2026_, 3);
v_moreServerOptions_2032_ = lean_ctor_get(v_cfg_2026_, 4);
v_weakLeancArgs_2033_ = lean_ctor_get(v_cfg_2026_, 5);
v_moreLinkObjs_2034_ = lean_ctor_get(v_cfg_2026_, 6);
v_moreLinkLibs_2035_ = lean_ctor_get(v_cfg_2026_, 7);
v_moreLinkArgs_2036_ = lean_ctor_get(v_cfg_2026_, 8);
v_weakLinkArgs_2037_ = lean_ctor_get(v_cfg_2026_, 9);
v_backend_2038_ = lean_ctor_get_uint8(v_cfg_2026_, sizeof(void*)*13 + 1);
v_platformIndependent_2039_ = lean_ctor_get(v_cfg_2026_, 10);
v_dynlibs_2040_ = lean_ctor_get(v_cfg_2026_, 11);
v_plugins_2041_ = lean_ctor_get(v_cfg_2026_, 12);
v_requiresModuleSystem_2042_ = lean_ctor_get_uint8(v_cfg_2026_, sizeof(void*)*13 + 3);
v_allowNonModules_2043_ = lean_ctor_get_uint8(v_cfg_2026_, sizeof(void*)*13 + 4);
v_isSharedCheck_2050_ = !lean_is_exclusive(v_cfg_2026_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v_cfg_2026_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_plugins_2041_);
lean_inc(v_dynlibs_2040_);
lean_inc(v_platformIndependent_2039_);
lean_inc(v_weakLinkArgs_2037_);
lean_inc(v_moreLinkArgs_2036_);
lean_inc(v_moreLinkLibs_2035_);
lean_inc(v_moreLinkObjs_2034_);
lean_inc(v_weakLeancArgs_2033_);
lean_inc(v_moreServerOptions_2032_);
lean_inc(v_moreLeancArgs_2031_);
lean_inc(v_weakLeanArgs_2030_);
lean_inc(v_moreLeanArgs_2029_);
lean_inc(v_leanOptions_2028_);
lean_dec(v_cfg_2026_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_leanOptions_2028_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_moreLeanArgs_2029_);
lean_ctor_set(v_reuseFailAlloc_2049_, 2, v_weakLeanArgs_2030_);
lean_ctor_set(v_reuseFailAlloc_2049_, 3, v_moreLeancArgs_2031_);
lean_ctor_set(v_reuseFailAlloc_2049_, 4, v_moreServerOptions_2032_);
lean_ctor_set(v_reuseFailAlloc_2049_, 5, v_weakLeancArgs_2033_);
lean_ctor_set(v_reuseFailAlloc_2049_, 6, v_moreLinkObjs_2034_);
lean_ctor_set(v_reuseFailAlloc_2049_, 7, v_moreLinkLibs_2035_);
lean_ctor_set(v_reuseFailAlloc_2049_, 8, v_moreLinkArgs_2036_);
lean_ctor_set(v_reuseFailAlloc_2049_, 9, v_weakLinkArgs_2037_);
lean_ctor_set(v_reuseFailAlloc_2049_, 10, v_platformIndependent_2039_);
lean_ctor_set(v_reuseFailAlloc_2049_, 11, v_dynlibs_2040_);
lean_ctor_set(v_reuseFailAlloc_2049_, 12, v_plugins_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13, v_buildType_2027_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 1, v_backend_2038_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2042_);
lean_ctor_set_uint8(v_reuseFailAlloc_2049_, sizeof(void*)*13 + 4, v_allowNonModules_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*13 + 2, v_val_2025_);
return v___x_2048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__1___boxed(lean_object* v_val_2051_, lean_object* v_cfg_2052_){
_start:
{
uint8_t v_val_88__boxed_2053_; lean_object* v_res_2054_; 
v_val_88__boxed_2053_ = lean_unbox(v_val_2051_);
v_res_2054_ = l_Lake_LeanConfig_precompileImports___proj___lam__1(v_val_88__boxed_2053_, v_cfg_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__2(lean_object* v_f_2055_, lean_object* v_cfg_2056_){
_start:
{
uint8_t v_buildType_2057_; lean_object* v_leanOptions_2058_; lean_object* v_moreLeanArgs_2059_; lean_object* v_weakLeanArgs_2060_; lean_object* v_moreLeancArgs_2061_; lean_object* v_moreServerOptions_2062_; lean_object* v_weakLeancArgs_2063_; lean_object* v_moreLinkObjs_2064_; lean_object* v_moreLinkLibs_2065_; lean_object* v_moreLinkArgs_2066_; lean_object* v_weakLinkArgs_2067_; uint8_t v_backend_2068_; lean_object* v_platformIndependent_2069_; uint8_t v_precompileImports_2070_; lean_object* v_dynlibs_2071_; lean_object* v_plugins_2072_; uint8_t v_requiresModuleSystem_2073_; uint8_t v_allowNonModules_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2084_; 
v_buildType_2057_ = lean_ctor_get_uint8(v_cfg_2056_, sizeof(void*)*13);
v_leanOptions_2058_ = lean_ctor_get(v_cfg_2056_, 0);
v_moreLeanArgs_2059_ = lean_ctor_get(v_cfg_2056_, 1);
v_weakLeanArgs_2060_ = lean_ctor_get(v_cfg_2056_, 2);
v_moreLeancArgs_2061_ = lean_ctor_get(v_cfg_2056_, 3);
v_moreServerOptions_2062_ = lean_ctor_get(v_cfg_2056_, 4);
v_weakLeancArgs_2063_ = lean_ctor_get(v_cfg_2056_, 5);
v_moreLinkObjs_2064_ = lean_ctor_get(v_cfg_2056_, 6);
v_moreLinkLibs_2065_ = lean_ctor_get(v_cfg_2056_, 7);
v_moreLinkArgs_2066_ = lean_ctor_get(v_cfg_2056_, 8);
v_weakLinkArgs_2067_ = lean_ctor_get(v_cfg_2056_, 9);
v_backend_2068_ = lean_ctor_get_uint8(v_cfg_2056_, sizeof(void*)*13 + 1);
v_platformIndependent_2069_ = lean_ctor_get(v_cfg_2056_, 10);
v_precompileImports_2070_ = lean_ctor_get_uint8(v_cfg_2056_, sizeof(void*)*13 + 2);
v_dynlibs_2071_ = lean_ctor_get(v_cfg_2056_, 11);
v_plugins_2072_ = lean_ctor_get(v_cfg_2056_, 12);
v_requiresModuleSystem_2073_ = lean_ctor_get_uint8(v_cfg_2056_, sizeof(void*)*13 + 3);
v_allowNonModules_2074_ = lean_ctor_get_uint8(v_cfg_2056_, sizeof(void*)*13 + 4);
v_isSharedCheck_2084_ = !lean_is_exclusive(v_cfg_2056_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2076_ = v_cfg_2056_;
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_plugins_2072_);
lean_inc(v_dynlibs_2071_);
lean_inc(v_platformIndependent_2069_);
lean_inc(v_weakLinkArgs_2067_);
lean_inc(v_moreLinkArgs_2066_);
lean_inc(v_moreLinkLibs_2065_);
lean_inc(v_moreLinkObjs_2064_);
lean_inc(v_weakLeancArgs_2063_);
lean_inc(v_moreServerOptions_2062_);
lean_inc(v_moreLeancArgs_2061_);
lean_inc(v_weakLeanArgs_2060_);
lean_inc(v_moreLeanArgs_2059_);
lean_inc(v_leanOptions_2058_);
lean_dec(v_cfg_2056_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2084_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2078_ = lean_box(v_precompileImports_2070_);
v___x_2079_ = lean_apply_1(v_f_2055_, v___x_2078_);
if (v_isShared_2077_ == 0)
{
v___x_2081_ = v___x_2076_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_leanOptions_2058_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_moreLeanArgs_2059_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_weakLeanArgs_2060_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_moreLeancArgs_2061_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v_moreServerOptions_2062_);
lean_ctor_set(v_reuseFailAlloc_2083_, 5, v_weakLeancArgs_2063_);
lean_ctor_set(v_reuseFailAlloc_2083_, 6, v_moreLinkObjs_2064_);
lean_ctor_set(v_reuseFailAlloc_2083_, 7, v_moreLinkLibs_2065_);
lean_ctor_set(v_reuseFailAlloc_2083_, 8, v_moreLinkArgs_2066_);
lean_ctor_set(v_reuseFailAlloc_2083_, 9, v_weakLinkArgs_2067_);
lean_ctor_set(v_reuseFailAlloc_2083_, 10, v_platformIndependent_2069_);
lean_ctor_set(v_reuseFailAlloc_2083_, 11, v_dynlibs_2071_);
lean_ctor_set(v_reuseFailAlloc_2083_, 12, v_plugins_2072_);
lean_ctor_set_uint8(v_reuseFailAlloc_2083_, sizeof(void*)*13, v_buildType_2057_);
lean_ctor_set_uint8(v_reuseFailAlloc_2083_, sizeof(void*)*13 + 1, v_backend_2068_);
v___x_2081_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_unbox(v___x_2079_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*13 + 2, v___x_2082_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2073_);
lean_ctor_set_uint8(v___x_2081_, sizeof(void*)*13 + 4, v_allowNonModules_2074_);
return v___x_2081_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_precompileImports___proj___lam__3(lean_object* v_x_2085_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = 0;
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_precompileImports___proj___lam__3___boxed(lean_object* v_x_2087_){
_start:
{
uint8_t v_res_2088_; lean_object* v_r_2089_; 
v_res_2088_ = l_Lake_LeanConfig_precompileImports___proj___lam__3(v_x_2087_);
lean_dec_ref(v_x_2087_);
v_r_2089_ = lean_box(v_res_2088_);
return v_r_2089_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_2101_){
_start:
{
lean_object* v_dynlibs_2102_; 
v_dynlibs_2102_ = lean_ctor_get(v_cfg_2101_, 11);
lean_inc_ref(v_dynlibs_2102_);
return v_dynlibs_2102_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_2103_);
lean_dec_ref(v_cfg_2103_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_2105_, lean_object* v_cfg_2106_){
_start:
{
uint8_t v_buildType_2107_; lean_object* v_leanOptions_2108_; lean_object* v_moreLeanArgs_2109_; lean_object* v_weakLeanArgs_2110_; lean_object* v_moreLeancArgs_2111_; lean_object* v_moreServerOptions_2112_; lean_object* v_weakLeancArgs_2113_; lean_object* v_moreLinkObjs_2114_; lean_object* v_moreLinkLibs_2115_; lean_object* v_moreLinkArgs_2116_; lean_object* v_weakLinkArgs_2117_; uint8_t v_backend_2118_; lean_object* v_platformIndependent_2119_; uint8_t v_precompileImports_2120_; lean_object* v_plugins_2121_; uint8_t v_requiresModuleSystem_2122_; uint8_t v_allowNonModules_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
v_buildType_2107_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*13);
v_leanOptions_2108_ = lean_ctor_get(v_cfg_2106_, 0);
v_moreLeanArgs_2109_ = lean_ctor_get(v_cfg_2106_, 1);
v_weakLeanArgs_2110_ = lean_ctor_get(v_cfg_2106_, 2);
v_moreLeancArgs_2111_ = lean_ctor_get(v_cfg_2106_, 3);
v_moreServerOptions_2112_ = lean_ctor_get(v_cfg_2106_, 4);
v_weakLeancArgs_2113_ = lean_ctor_get(v_cfg_2106_, 5);
v_moreLinkObjs_2114_ = lean_ctor_get(v_cfg_2106_, 6);
v_moreLinkLibs_2115_ = lean_ctor_get(v_cfg_2106_, 7);
v_moreLinkArgs_2116_ = lean_ctor_get(v_cfg_2106_, 8);
v_weakLinkArgs_2117_ = lean_ctor_get(v_cfg_2106_, 9);
v_backend_2118_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*13 + 1);
v_platformIndependent_2119_ = lean_ctor_get(v_cfg_2106_, 10);
v_precompileImports_2120_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*13 + 2);
v_plugins_2121_ = lean_ctor_get(v_cfg_2106_, 12);
v_requiresModuleSystem_2122_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*13 + 3);
v_allowNonModules_2123_ = lean_ctor_get_uint8(v_cfg_2106_, sizeof(void*)*13 + 4);
v_isSharedCheck_2130_ = !lean_is_exclusive(v_cfg_2106_);
if (v_isSharedCheck_2130_ == 0)
{
lean_object* v_unused_2131_; 
v_unused_2131_ = lean_ctor_get(v_cfg_2106_, 11);
lean_dec(v_unused_2131_);
v___x_2125_ = v_cfg_2106_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_plugins_2121_);
lean_inc(v_platformIndependent_2119_);
lean_inc(v_weakLinkArgs_2117_);
lean_inc(v_moreLinkArgs_2116_);
lean_inc(v_moreLinkLibs_2115_);
lean_inc(v_moreLinkObjs_2114_);
lean_inc(v_weakLeancArgs_2113_);
lean_inc(v_moreServerOptions_2112_);
lean_inc(v_moreLeancArgs_2111_);
lean_inc(v_weakLeanArgs_2110_);
lean_inc(v_moreLeanArgs_2109_);
lean_inc(v_leanOptions_2108_);
lean_dec(v_cfg_2106_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2128_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 11, v_val_2105_);
v___x_2128_ = v___x_2125_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_leanOptions_2108_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_moreLeanArgs_2109_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_weakLeanArgs_2110_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_moreLeancArgs_2111_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_moreServerOptions_2112_);
lean_ctor_set(v_reuseFailAlloc_2129_, 5, v_weakLeancArgs_2113_);
lean_ctor_set(v_reuseFailAlloc_2129_, 6, v_moreLinkObjs_2114_);
lean_ctor_set(v_reuseFailAlloc_2129_, 7, v_moreLinkLibs_2115_);
lean_ctor_set(v_reuseFailAlloc_2129_, 8, v_moreLinkArgs_2116_);
lean_ctor_set(v_reuseFailAlloc_2129_, 9, v_weakLinkArgs_2117_);
lean_ctor_set(v_reuseFailAlloc_2129_, 10, v_platformIndependent_2119_);
lean_ctor_set(v_reuseFailAlloc_2129_, 11, v_val_2105_);
lean_ctor_set(v_reuseFailAlloc_2129_, 12, v_plugins_2121_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*13, v_buildType_2107_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*13 + 1, v_backend_2118_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*13 + 2, v_precompileImports_2120_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2122_);
lean_ctor_set_uint8(v_reuseFailAlloc_2129_, sizeof(void*)*13 + 4, v_allowNonModules_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_2132_, lean_object* v_cfg_2133_){
_start:
{
uint8_t v_buildType_2134_; lean_object* v_leanOptions_2135_; lean_object* v_moreLeanArgs_2136_; lean_object* v_weakLeanArgs_2137_; lean_object* v_moreLeancArgs_2138_; lean_object* v_moreServerOptions_2139_; lean_object* v_weakLeancArgs_2140_; lean_object* v_moreLinkObjs_2141_; lean_object* v_moreLinkLibs_2142_; lean_object* v_moreLinkArgs_2143_; lean_object* v_weakLinkArgs_2144_; uint8_t v_backend_2145_; lean_object* v_platformIndependent_2146_; uint8_t v_precompileImports_2147_; lean_object* v_dynlibs_2148_; lean_object* v_plugins_2149_; uint8_t v_requiresModuleSystem_2150_; uint8_t v_allowNonModules_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2159_; 
v_buildType_2134_ = lean_ctor_get_uint8(v_cfg_2133_, sizeof(void*)*13);
v_leanOptions_2135_ = lean_ctor_get(v_cfg_2133_, 0);
v_moreLeanArgs_2136_ = lean_ctor_get(v_cfg_2133_, 1);
v_weakLeanArgs_2137_ = lean_ctor_get(v_cfg_2133_, 2);
v_moreLeancArgs_2138_ = lean_ctor_get(v_cfg_2133_, 3);
v_moreServerOptions_2139_ = lean_ctor_get(v_cfg_2133_, 4);
v_weakLeancArgs_2140_ = lean_ctor_get(v_cfg_2133_, 5);
v_moreLinkObjs_2141_ = lean_ctor_get(v_cfg_2133_, 6);
v_moreLinkLibs_2142_ = lean_ctor_get(v_cfg_2133_, 7);
v_moreLinkArgs_2143_ = lean_ctor_get(v_cfg_2133_, 8);
v_weakLinkArgs_2144_ = lean_ctor_get(v_cfg_2133_, 9);
v_backend_2145_ = lean_ctor_get_uint8(v_cfg_2133_, sizeof(void*)*13 + 1);
v_platformIndependent_2146_ = lean_ctor_get(v_cfg_2133_, 10);
v_precompileImports_2147_ = lean_ctor_get_uint8(v_cfg_2133_, sizeof(void*)*13 + 2);
v_dynlibs_2148_ = lean_ctor_get(v_cfg_2133_, 11);
v_plugins_2149_ = lean_ctor_get(v_cfg_2133_, 12);
v_requiresModuleSystem_2150_ = lean_ctor_get_uint8(v_cfg_2133_, sizeof(void*)*13 + 3);
v_allowNonModules_2151_ = lean_ctor_get_uint8(v_cfg_2133_, sizeof(void*)*13 + 4);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_cfg_2133_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2153_ = v_cfg_2133_;
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_plugins_2149_);
lean_inc(v_dynlibs_2148_);
lean_inc(v_platformIndependent_2146_);
lean_inc(v_weakLinkArgs_2144_);
lean_inc(v_moreLinkArgs_2143_);
lean_inc(v_moreLinkLibs_2142_);
lean_inc(v_moreLinkObjs_2141_);
lean_inc(v_weakLeancArgs_2140_);
lean_inc(v_moreServerOptions_2139_);
lean_inc(v_moreLeancArgs_2138_);
lean_inc(v_weakLeanArgs_2137_);
lean_inc(v_moreLeanArgs_2136_);
lean_inc(v_leanOptions_2135_);
lean_dec(v_cfg_2133_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2157_; 
v___x_2155_ = lean_apply_1(v_f_2132_, v_dynlibs_2148_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 11, v___x_2155_);
v___x_2157_ = v___x_2153_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_leanOptions_2135_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_moreLeanArgs_2136_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_weakLeanArgs_2137_);
lean_ctor_set(v_reuseFailAlloc_2158_, 3, v_moreLeancArgs_2138_);
lean_ctor_set(v_reuseFailAlloc_2158_, 4, v_moreServerOptions_2139_);
lean_ctor_set(v_reuseFailAlloc_2158_, 5, v_weakLeancArgs_2140_);
lean_ctor_set(v_reuseFailAlloc_2158_, 6, v_moreLinkObjs_2141_);
lean_ctor_set(v_reuseFailAlloc_2158_, 7, v_moreLinkLibs_2142_);
lean_ctor_set(v_reuseFailAlloc_2158_, 8, v_moreLinkArgs_2143_);
lean_ctor_set(v_reuseFailAlloc_2158_, 9, v_weakLinkArgs_2144_);
lean_ctor_set(v_reuseFailAlloc_2158_, 10, v_platformIndependent_2146_);
lean_ctor_set(v_reuseFailAlloc_2158_, 11, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2158_, 12, v_plugins_2149_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*13, v_buildType_2134_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*13 + 1, v_backend_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*13 + 2, v_precompileImports_2147_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2150_);
lean_ctor_set_uint8(v_reuseFailAlloc_2158_, sizeof(void*)*13 + 4, v_allowNonModules_2151_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_2170_){
_start:
{
lean_object* v_plugins_2171_; 
v_plugins_2171_ = lean_ctor_get(v_cfg_2170_, 12);
lean_inc_ref(v_plugins_2171_);
return v_plugins_2171_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_2172_);
lean_dec_ref(v_cfg_2172_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_2174_, lean_object* v_cfg_2175_){
_start:
{
uint8_t v_buildType_2176_; lean_object* v_leanOptions_2177_; lean_object* v_moreLeanArgs_2178_; lean_object* v_weakLeanArgs_2179_; lean_object* v_moreLeancArgs_2180_; lean_object* v_moreServerOptions_2181_; lean_object* v_weakLeancArgs_2182_; lean_object* v_moreLinkObjs_2183_; lean_object* v_moreLinkLibs_2184_; lean_object* v_moreLinkArgs_2185_; lean_object* v_weakLinkArgs_2186_; uint8_t v_backend_2187_; lean_object* v_platformIndependent_2188_; uint8_t v_precompileImports_2189_; lean_object* v_dynlibs_2190_; uint8_t v_requiresModuleSystem_2191_; uint8_t v_allowNonModules_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
v_buildType_2176_ = lean_ctor_get_uint8(v_cfg_2175_, sizeof(void*)*13);
v_leanOptions_2177_ = lean_ctor_get(v_cfg_2175_, 0);
v_moreLeanArgs_2178_ = lean_ctor_get(v_cfg_2175_, 1);
v_weakLeanArgs_2179_ = lean_ctor_get(v_cfg_2175_, 2);
v_moreLeancArgs_2180_ = lean_ctor_get(v_cfg_2175_, 3);
v_moreServerOptions_2181_ = lean_ctor_get(v_cfg_2175_, 4);
v_weakLeancArgs_2182_ = lean_ctor_get(v_cfg_2175_, 5);
v_moreLinkObjs_2183_ = lean_ctor_get(v_cfg_2175_, 6);
v_moreLinkLibs_2184_ = lean_ctor_get(v_cfg_2175_, 7);
v_moreLinkArgs_2185_ = lean_ctor_get(v_cfg_2175_, 8);
v_weakLinkArgs_2186_ = lean_ctor_get(v_cfg_2175_, 9);
v_backend_2187_ = lean_ctor_get_uint8(v_cfg_2175_, sizeof(void*)*13 + 1);
v_platformIndependent_2188_ = lean_ctor_get(v_cfg_2175_, 10);
v_precompileImports_2189_ = lean_ctor_get_uint8(v_cfg_2175_, sizeof(void*)*13 + 2);
v_dynlibs_2190_ = lean_ctor_get(v_cfg_2175_, 11);
v_requiresModuleSystem_2191_ = lean_ctor_get_uint8(v_cfg_2175_, sizeof(void*)*13 + 3);
v_allowNonModules_2192_ = lean_ctor_get_uint8(v_cfg_2175_, sizeof(void*)*13 + 4);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_cfg_2175_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v_cfg_2175_, 12);
lean_dec(v_unused_2200_);
v___x_2194_ = v_cfg_2175_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_dynlibs_2190_);
lean_inc(v_platformIndependent_2188_);
lean_inc(v_weakLinkArgs_2186_);
lean_inc(v_moreLinkArgs_2185_);
lean_inc(v_moreLinkLibs_2184_);
lean_inc(v_moreLinkObjs_2183_);
lean_inc(v_weakLeancArgs_2182_);
lean_inc(v_moreServerOptions_2181_);
lean_inc(v_moreLeancArgs_2180_);
lean_inc(v_weakLeanArgs_2179_);
lean_inc(v_moreLeanArgs_2178_);
lean_inc(v_leanOptions_2177_);
lean_dec(v_cfg_2175_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 12, v_val_2174_);
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_leanOptions_2177_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_moreLeanArgs_2178_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_weakLeanArgs_2179_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_moreLeancArgs_2180_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_moreServerOptions_2181_);
lean_ctor_set(v_reuseFailAlloc_2198_, 5, v_weakLeancArgs_2182_);
lean_ctor_set(v_reuseFailAlloc_2198_, 6, v_moreLinkObjs_2183_);
lean_ctor_set(v_reuseFailAlloc_2198_, 7, v_moreLinkLibs_2184_);
lean_ctor_set(v_reuseFailAlloc_2198_, 8, v_moreLinkArgs_2185_);
lean_ctor_set(v_reuseFailAlloc_2198_, 9, v_weakLinkArgs_2186_);
lean_ctor_set(v_reuseFailAlloc_2198_, 10, v_platformIndependent_2188_);
lean_ctor_set(v_reuseFailAlloc_2198_, 11, v_dynlibs_2190_);
lean_ctor_set(v_reuseFailAlloc_2198_, 12, v_val_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13, v_buildType_2176_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 1, v_backend_2187_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 2, v_precompileImports_2189_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2191_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*13 + 4, v_allowNonModules_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_2201_, lean_object* v_cfg_2202_){
_start:
{
uint8_t v_buildType_2203_; lean_object* v_leanOptions_2204_; lean_object* v_moreLeanArgs_2205_; lean_object* v_weakLeanArgs_2206_; lean_object* v_moreLeancArgs_2207_; lean_object* v_moreServerOptions_2208_; lean_object* v_weakLeancArgs_2209_; lean_object* v_moreLinkObjs_2210_; lean_object* v_moreLinkLibs_2211_; lean_object* v_moreLinkArgs_2212_; lean_object* v_weakLinkArgs_2213_; uint8_t v_backend_2214_; lean_object* v_platformIndependent_2215_; uint8_t v_precompileImports_2216_; lean_object* v_dynlibs_2217_; lean_object* v_plugins_2218_; uint8_t v_requiresModuleSystem_2219_; uint8_t v_allowNonModules_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2228_; 
v_buildType_2203_ = lean_ctor_get_uint8(v_cfg_2202_, sizeof(void*)*13);
v_leanOptions_2204_ = lean_ctor_get(v_cfg_2202_, 0);
v_moreLeanArgs_2205_ = lean_ctor_get(v_cfg_2202_, 1);
v_weakLeanArgs_2206_ = lean_ctor_get(v_cfg_2202_, 2);
v_moreLeancArgs_2207_ = lean_ctor_get(v_cfg_2202_, 3);
v_moreServerOptions_2208_ = lean_ctor_get(v_cfg_2202_, 4);
v_weakLeancArgs_2209_ = lean_ctor_get(v_cfg_2202_, 5);
v_moreLinkObjs_2210_ = lean_ctor_get(v_cfg_2202_, 6);
v_moreLinkLibs_2211_ = lean_ctor_get(v_cfg_2202_, 7);
v_moreLinkArgs_2212_ = lean_ctor_get(v_cfg_2202_, 8);
v_weakLinkArgs_2213_ = lean_ctor_get(v_cfg_2202_, 9);
v_backend_2214_ = lean_ctor_get_uint8(v_cfg_2202_, sizeof(void*)*13 + 1);
v_platformIndependent_2215_ = lean_ctor_get(v_cfg_2202_, 10);
v_precompileImports_2216_ = lean_ctor_get_uint8(v_cfg_2202_, sizeof(void*)*13 + 2);
v_dynlibs_2217_ = lean_ctor_get(v_cfg_2202_, 11);
v_plugins_2218_ = lean_ctor_get(v_cfg_2202_, 12);
v_requiresModuleSystem_2219_ = lean_ctor_get_uint8(v_cfg_2202_, sizeof(void*)*13 + 3);
v_allowNonModules_2220_ = lean_ctor_get_uint8(v_cfg_2202_, sizeof(void*)*13 + 4);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_cfg_2202_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2222_ = v_cfg_2202_;
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_plugins_2218_);
lean_inc(v_dynlibs_2217_);
lean_inc(v_platformIndependent_2215_);
lean_inc(v_weakLinkArgs_2213_);
lean_inc(v_moreLinkArgs_2212_);
lean_inc(v_moreLinkLibs_2211_);
lean_inc(v_moreLinkObjs_2210_);
lean_inc(v_weakLeancArgs_2209_);
lean_inc(v_moreServerOptions_2208_);
lean_inc(v_moreLeancArgs_2207_);
lean_inc(v_weakLeanArgs_2206_);
lean_inc(v_moreLeanArgs_2205_);
lean_inc(v_leanOptions_2204_);
lean_dec(v_cfg_2202_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_apply_1(v_f_2201_, v_plugins_2218_);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 12, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_leanOptions_2204_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_moreLeanArgs_2205_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_weakLeanArgs_2206_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_moreLeancArgs_2207_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_moreServerOptions_2208_);
lean_ctor_set(v_reuseFailAlloc_2227_, 5, v_weakLeancArgs_2209_);
lean_ctor_set(v_reuseFailAlloc_2227_, 6, v_moreLinkObjs_2210_);
lean_ctor_set(v_reuseFailAlloc_2227_, 7, v_moreLinkLibs_2211_);
lean_ctor_set(v_reuseFailAlloc_2227_, 8, v_moreLinkArgs_2212_);
lean_ctor_set(v_reuseFailAlloc_2227_, 9, v_weakLinkArgs_2213_);
lean_ctor_set(v_reuseFailAlloc_2227_, 10, v_platformIndependent_2215_);
lean_ctor_set(v_reuseFailAlloc_2227_, 11, v_dynlibs_2217_);
lean_ctor_set(v_reuseFailAlloc_2227_, 12, v___x_2224_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13, v_buildType_2203_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 1, v_backend_2214_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 2, v_precompileImports_2216_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2219_);
lean_ctor_set_uint8(v_reuseFailAlloc_2227_, sizeof(void*)*13 + 4, v_allowNonModules_2220_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object* v_cfg_2239_){
_start:
{
uint8_t v_requiresModuleSystem_2240_; 
v_requiresModuleSystem_2240_ = lean_ctor_get_uint8(v_cfg_2239_, sizeof(void*)*13 + 3);
return v_requiresModuleSystem_2240_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object* v_cfg_2241_){
_start:
{
uint8_t v_res_2242_; lean_object* v_r_2243_; 
v_res_2242_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2241_);
lean_dec_ref(v_cfg_2241_);
v_r_2243_ = lean_box(v_res_2242_);
return v_r_2243_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t v_val_2244_, lean_object* v_cfg_2245_){
_start:
{
uint8_t v_buildType_2246_; lean_object* v_leanOptions_2247_; lean_object* v_moreLeanArgs_2248_; lean_object* v_weakLeanArgs_2249_; lean_object* v_moreLeancArgs_2250_; lean_object* v_moreServerOptions_2251_; lean_object* v_weakLeancArgs_2252_; lean_object* v_moreLinkObjs_2253_; lean_object* v_moreLinkLibs_2254_; lean_object* v_moreLinkArgs_2255_; lean_object* v_weakLinkArgs_2256_; uint8_t v_backend_2257_; lean_object* v_platformIndependent_2258_; uint8_t v_precompileImports_2259_; lean_object* v_dynlibs_2260_; lean_object* v_plugins_2261_; uint8_t v_allowNonModules_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
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
v_allowNonModules_2262_ = lean_ctor_get_uint8(v_cfg_2245_, sizeof(void*)*13 + 4);
v_isSharedCheck_2269_ = !lean_is_exclusive(v_cfg_2245_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v_cfg_2245_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
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
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_leanOptions_2247_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_moreLeanArgs_2248_);
lean_ctor_set(v_reuseFailAlloc_2268_, 2, v_weakLeanArgs_2249_);
lean_ctor_set(v_reuseFailAlloc_2268_, 3, v_moreLeancArgs_2250_);
lean_ctor_set(v_reuseFailAlloc_2268_, 4, v_moreServerOptions_2251_);
lean_ctor_set(v_reuseFailAlloc_2268_, 5, v_weakLeancArgs_2252_);
lean_ctor_set(v_reuseFailAlloc_2268_, 6, v_moreLinkObjs_2253_);
lean_ctor_set(v_reuseFailAlloc_2268_, 7, v_moreLinkLibs_2254_);
lean_ctor_set(v_reuseFailAlloc_2268_, 8, v_moreLinkArgs_2255_);
lean_ctor_set(v_reuseFailAlloc_2268_, 9, v_weakLinkArgs_2256_);
lean_ctor_set(v_reuseFailAlloc_2268_, 10, v_platformIndependent_2258_);
lean_ctor_set(v_reuseFailAlloc_2268_, 11, v_dynlibs_2260_);
lean_ctor_set(v_reuseFailAlloc_2268_, 12, v_plugins_2261_);
lean_ctor_set_uint8(v_reuseFailAlloc_2268_, sizeof(void*)*13, v_buildType_2246_);
lean_ctor_set_uint8(v_reuseFailAlloc_2268_, sizeof(void*)*13 + 1, v_backend_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2268_, sizeof(void*)*13 + 2, v_precompileImports_2259_);
lean_ctor_set_uint8(v_reuseFailAlloc_2268_, sizeof(void*)*13 + 4, v_allowNonModules_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
lean_ctor_set_uint8(v___x_2267_, sizeof(void*)*13 + 3, v_val_2244_);
return v___x_2267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object* v_val_2270_, lean_object* v_cfg_2271_){
_start:
{
uint8_t v_val_88__boxed_2272_; lean_object* v_res_2273_; 
v_val_88__boxed_2272_ = lean_unbox(v_val_2270_);
v_res_2273_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_88__boxed_2272_, v_cfg_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object* v_f_2274_, lean_object* v_cfg_2275_){
_start:
{
uint8_t v_buildType_2276_; lean_object* v_leanOptions_2277_; lean_object* v_moreLeanArgs_2278_; lean_object* v_weakLeanArgs_2279_; lean_object* v_moreLeancArgs_2280_; lean_object* v_moreServerOptions_2281_; lean_object* v_weakLeancArgs_2282_; lean_object* v_moreLinkObjs_2283_; lean_object* v_moreLinkLibs_2284_; lean_object* v_moreLinkArgs_2285_; lean_object* v_weakLinkArgs_2286_; uint8_t v_backend_2287_; lean_object* v_platformIndependent_2288_; uint8_t v_precompileImports_2289_; lean_object* v_dynlibs_2290_; lean_object* v_plugins_2291_; uint8_t v_requiresModuleSystem_2292_; uint8_t v_allowNonModules_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2303_; 
v_buildType_2276_ = lean_ctor_get_uint8(v_cfg_2275_, sizeof(void*)*13);
v_leanOptions_2277_ = lean_ctor_get(v_cfg_2275_, 0);
v_moreLeanArgs_2278_ = lean_ctor_get(v_cfg_2275_, 1);
v_weakLeanArgs_2279_ = lean_ctor_get(v_cfg_2275_, 2);
v_moreLeancArgs_2280_ = lean_ctor_get(v_cfg_2275_, 3);
v_moreServerOptions_2281_ = lean_ctor_get(v_cfg_2275_, 4);
v_weakLeancArgs_2282_ = lean_ctor_get(v_cfg_2275_, 5);
v_moreLinkObjs_2283_ = lean_ctor_get(v_cfg_2275_, 6);
v_moreLinkLibs_2284_ = lean_ctor_get(v_cfg_2275_, 7);
v_moreLinkArgs_2285_ = lean_ctor_get(v_cfg_2275_, 8);
v_weakLinkArgs_2286_ = lean_ctor_get(v_cfg_2275_, 9);
v_backend_2287_ = lean_ctor_get_uint8(v_cfg_2275_, sizeof(void*)*13 + 1);
v_platformIndependent_2288_ = lean_ctor_get(v_cfg_2275_, 10);
v_precompileImports_2289_ = lean_ctor_get_uint8(v_cfg_2275_, sizeof(void*)*13 + 2);
v_dynlibs_2290_ = lean_ctor_get(v_cfg_2275_, 11);
v_plugins_2291_ = lean_ctor_get(v_cfg_2275_, 12);
v_requiresModuleSystem_2292_ = lean_ctor_get_uint8(v_cfg_2275_, sizeof(void*)*13 + 3);
v_allowNonModules_2293_ = lean_ctor_get_uint8(v_cfg_2275_, sizeof(void*)*13 + 4);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_cfg_2275_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2295_ = v_cfg_2275_;
v_isShared_2296_ = v_isSharedCheck_2303_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_plugins_2291_);
lean_inc(v_dynlibs_2290_);
lean_inc(v_platformIndependent_2288_);
lean_inc(v_weakLinkArgs_2286_);
lean_inc(v_moreLinkArgs_2285_);
lean_inc(v_moreLinkLibs_2284_);
lean_inc(v_moreLinkObjs_2283_);
lean_inc(v_weakLeancArgs_2282_);
lean_inc(v_moreServerOptions_2281_);
lean_inc(v_moreLeancArgs_2280_);
lean_inc(v_weakLeanArgs_2279_);
lean_inc(v_moreLeanArgs_2278_);
lean_inc(v_leanOptions_2277_);
lean_dec(v_cfg_2275_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2303_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2297_ = lean_box(v_requiresModuleSystem_2292_);
v___x_2298_ = lean_apply_1(v_f_2274_, v___x_2297_);
if (v_isShared_2296_ == 0)
{
v___x_2300_ = v___x_2295_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_leanOptions_2277_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_moreLeanArgs_2278_);
lean_ctor_set(v_reuseFailAlloc_2302_, 2, v_weakLeanArgs_2279_);
lean_ctor_set(v_reuseFailAlloc_2302_, 3, v_moreLeancArgs_2280_);
lean_ctor_set(v_reuseFailAlloc_2302_, 4, v_moreServerOptions_2281_);
lean_ctor_set(v_reuseFailAlloc_2302_, 5, v_weakLeancArgs_2282_);
lean_ctor_set(v_reuseFailAlloc_2302_, 6, v_moreLinkObjs_2283_);
lean_ctor_set(v_reuseFailAlloc_2302_, 7, v_moreLinkLibs_2284_);
lean_ctor_set(v_reuseFailAlloc_2302_, 8, v_moreLinkArgs_2285_);
lean_ctor_set(v_reuseFailAlloc_2302_, 9, v_weakLinkArgs_2286_);
lean_ctor_set(v_reuseFailAlloc_2302_, 10, v_platformIndependent_2288_);
lean_ctor_set(v_reuseFailAlloc_2302_, 11, v_dynlibs_2290_);
lean_ctor_set(v_reuseFailAlloc_2302_, 12, v_plugins_2291_);
lean_ctor_set_uint8(v_reuseFailAlloc_2302_, sizeof(void*)*13, v_buildType_2276_);
lean_ctor_set_uint8(v_reuseFailAlloc_2302_, sizeof(void*)*13 + 1, v_backend_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2302_, sizeof(void*)*13 + 2, v_precompileImports_2289_);
v___x_2300_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
uint8_t v___x_2301_; 
v___x_2301_ = lean_unbox(v___x_2298_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*13 + 3, v___x_2301_);
lean_ctor_set_uint8(v___x_2300_, sizeof(void*)*13 + 4, v_allowNonModules_2293_);
return v___x_2300_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object* v_cfg_2314_){
_start:
{
uint8_t v_allowNonModules_2315_; 
v_allowNonModules_2315_ = lean_ctor_get_uint8(v_cfg_2314_, sizeof(void*)*13 + 4);
return v_allowNonModules_2315_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object* v_cfg_2316_){
_start:
{
uint8_t v_res_2317_; lean_object* v_r_2318_; 
v_res_2317_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2316_);
lean_dec_ref(v_cfg_2316_);
v_r_2318_ = lean_box(v_res_2317_);
return v_r_2318_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t v_val_2319_, lean_object* v_cfg_2320_){
_start:
{
uint8_t v_buildType_2321_; lean_object* v_leanOptions_2322_; lean_object* v_moreLeanArgs_2323_; lean_object* v_weakLeanArgs_2324_; lean_object* v_moreLeancArgs_2325_; lean_object* v_moreServerOptions_2326_; lean_object* v_weakLeancArgs_2327_; lean_object* v_moreLinkObjs_2328_; lean_object* v_moreLinkLibs_2329_; lean_object* v_moreLinkArgs_2330_; lean_object* v_weakLinkArgs_2331_; uint8_t v_backend_2332_; lean_object* v_platformIndependent_2333_; uint8_t v_precompileImports_2334_; lean_object* v_dynlibs_2335_; lean_object* v_plugins_2336_; uint8_t v_requiresModuleSystem_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
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
v_isSharedCheck_2344_ = !lean_is_exclusive(v_cfg_2320_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v_cfg_2320_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
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
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_leanOptions_2322_);
lean_ctor_set(v_reuseFailAlloc_2343_, 1, v_moreLeanArgs_2323_);
lean_ctor_set(v_reuseFailAlloc_2343_, 2, v_weakLeanArgs_2324_);
lean_ctor_set(v_reuseFailAlloc_2343_, 3, v_moreLeancArgs_2325_);
lean_ctor_set(v_reuseFailAlloc_2343_, 4, v_moreServerOptions_2326_);
lean_ctor_set(v_reuseFailAlloc_2343_, 5, v_weakLeancArgs_2327_);
lean_ctor_set(v_reuseFailAlloc_2343_, 6, v_moreLinkObjs_2328_);
lean_ctor_set(v_reuseFailAlloc_2343_, 7, v_moreLinkLibs_2329_);
lean_ctor_set(v_reuseFailAlloc_2343_, 8, v_moreLinkArgs_2330_);
lean_ctor_set(v_reuseFailAlloc_2343_, 9, v_weakLinkArgs_2331_);
lean_ctor_set(v_reuseFailAlloc_2343_, 10, v_platformIndependent_2333_);
lean_ctor_set(v_reuseFailAlloc_2343_, 11, v_dynlibs_2335_);
lean_ctor_set(v_reuseFailAlloc_2343_, 12, v_plugins_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*13, v_buildType_2321_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*13 + 1, v_backend_2332_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*13 + 2, v_precompileImports_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2343_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*13 + 4, v_val_2319_);
return v___x_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object* v_val_2345_, lean_object* v_cfg_2346_){
_start:
{
uint8_t v_val_88__boxed_2347_; lean_object* v_res_2348_; 
v_val_88__boxed_2347_ = lean_unbox(v_val_2345_);
v_res_2348_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_88__boxed_2347_, v_cfg_2346_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object* v_f_2349_, lean_object* v_cfg_2350_){
_start:
{
uint8_t v_buildType_2351_; lean_object* v_leanOptions_2352_; lean_object* v_moreLeanArgs_2353_; lean_object* v_weakLeanArgs_2354_; lean_object* v_moreLeancArgs_2355_; lean_object* v_moreServerOptions_2356_; lean_object* v_weakLeancArgs_2357_; lean_object* v_moreLinkObjs_2358_; lean_object* v_moreLinkLibs_2359_; lean_object* v_moreLinkArgs_2360_; lean_object* v_weakLinkArgs_2361_; uint8_t v_backend_2362_; lean_object* v_platformIndependent_2363_; uint8_t v_precompileImports_2364_; lean_object* v_dynlibs_2365_; lean_object* v_plugins_2366_; uint8_t v_requiresModuleSystem_2367_; uint8_t v_allowNonModules_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2378_; 
v_buildType_2351_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*13);
v_leanOptions_2352_ = lean_ctor_get(v_cfg_2350_, 0);
v_moreLeanArgs_2353_ = lean_ctor_get(v_cfg_2350_, 1);
v_weakLeanArgs_2354_ = lean_ctor_get(v_cfg_2350_, 2);
v_moreLeancArgs_2355_ = lean_ctor_get(v_cfg_2350_, 3);
v_moreServerOptions_2356_ = lean_ctor_get(v_cfg_2350_, 4);
v_weakLeancArgs_2357_ = lean_ctor_get(v_cfg_2350_, 5);
v_moreLinkObjs_2358_ = lean_ctor_get(v_cfg_2350_, 6);
v_moreLinkLibs_2359_ = lean_ctor_get(v_cfg_2350_, 7);
v_moreLinkArgs_2360_ = lean_ctor_get(v_cfg_2350_, 8);
v_weakLinkArgs_2361_ = lean_ctor_get(v_cfg_2350_, 9);
v_backend_2362_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*13 + 1);
v_platformIndependent_2363_ = lean_ctor_get(v_cfg_2350_, 10);
v_precompileImports_2364_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*13 + 2);
v_dynlibs_2365_ = lean_ctor_get(v_cfg_2350_, 11);
v_plugins_2366_ = lean_ctor_get(v_cfg_2350_, 12);
v_requiresModuleSystem_2367_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*13 + 3);
v_allowNonModules_2368_ = lean_ctor_get_uint8(v_cfg_2350_, sizeof(void*)*13 + 4);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_cfg_2350_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2370_ = v_cfg_2350_;
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_plugins_2366_);
lean_inc(v_dynlibs_2365_);
lean_inc(v_platformIndependent_2363_);
lean_inc(v_weakLinkArgs_2361_);
lean_inc(v_moreLinkArgs_2360_);
lean_inc(v_moreLinkLibs_2359_);
lean_inc(v_moreLinkObjs_2358_);
lean_inc(v_weakLeancArgs_2357_);
lean_inc(v_moreServerOptions_2356_);
lean_inc(v_moreLeancArgs_2355_);
lean_inc(v_weakLeanArgs_2354_);
lean_inc(v_moreLeanArgs_2353_);
lean_inc(v_leanOptions_2352_);
lean_dec(v_cfg_2350_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2378_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2372_ = lean_box(v_allowNonModules_2368_);
v___x_2373_ = lean_apply_1(v_f_2349_, v___x_2372_);
if (v_isShared_2371_ == 0)
{
v___x_2375_ = v___x_2370_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 13, 5);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_leanOptions_2352_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_moreLeanArgs_2353_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_weakLeanArgs_2354_);
lean_ctor_set(v_reuseFailAlloc_2377_, 3, v_moreLeancArgs_2355_);
lean_ctor_set(v_reuseFailAlloc_2377_, 4, v_moreServerOptions_2356_);
lean_ctor_set(v_reuseFailAlloc_2377_, 5, v_weakLeancArgs_2357_);
lean_ctor_set(v_reuseFailAlloc_2377_, 6, v_moreLinkObjs_2358_);
lean_ctor_set(v_reuseFailAlloc_2377_, 7, v_moreLinkLibs_2359_);
lean_ctor_set(v_reuseFailAlloc_2377_, 8, v_moreLinkArgs_2360_);
lean_ctor_set(v_reuseFailAlloc_2377_, 9, v_weakLinkArgs_2361_);
lean_ctor_set(v_reuseFailAlloc_2377_, 10, v_platformIndependent_2363_);
lean_ctor_set(v_reuseFailAlloc_2377_, 11, v_dynlibs_2365_);
lean_ctor_set(v_reuseFailAlloc_2377_, 12, v_plugins_2366_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13, v_buildType_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 1, v_backend_2362_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 2, v_precompileImports_2364_);
lean_ctor_set_uint8(v_reuseFailAlloc_2377_, sizeof(void*)*13 + 3, v_requiresModuleSystem_2367_);
v___x_2375_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
uint8_t v___x_2376_; 
v___x_2376_ = lean_unbox(v___x_2373_);
lean_ctor_set_uint8(v___x_2375_, sizeof(void*)*13 + 4, v___x_2376_);
return v___x_2375_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2398_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2399_ = lean_array_push(v___x_2398_, v___x_2397_);
return v___x_2399_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2406_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2407_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2408_ = lean_array_push(v___x_2407_, v___x_2406_);
return v___x_2408_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2416_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2417_ = lean_array_push(v___x_2416_, v___x_2415_);
return v___x_2417_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2424_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2425_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2426_ = lean_array_push(v___x_2425_, v___x_2424_);
return v___x_2426_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2434_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2435_ = lean_array_push(v___x_2434_, v___x_2433_);
return v___x_2435_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2443_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2444_ = lean_array_push(v___x_2443_, v___x_2442_);
return v___x_2444_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2451_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2452_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2453_ = lean_array_push(v___x_2452_, v___x_2451_);
return v___x_2453_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2461_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2462_ = lean_array_push(v___x_2461_, v___x_2460_);
return v___x_2462_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2469_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2470_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2471_ = lean_array_push(v___x_2470_, v___x_2469_);
return v___x_2471_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2478_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2479_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2480_ = lean_array_push(v___x_2479_, v___x_2478_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2487_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2488_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2489_ = lean_array_push(v___x_2488_, v___x_2487_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2496_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2497_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2498_ = lean_array_push(v___x_2497_, v___x_2496_);
return v___x_2498_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2506_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2507_ = lean_array_push(v___x_2506_, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2515_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2516_ = lean_array_push(v___x_2515_, v___x_2514_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2523_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2524_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2525_ = lean_array_push(v___x_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__47));
v___x_2533_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
v___x_2534_ = lean_array_push(v___x_2533_, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__51(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__50));
v___x_2542_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__48, &l_Lake_LeanConfig___fields___closed__48_once, _init_l_Lake_LeanConfig___fields___closed__48);
v___x_2543_ = lean_array_push(v___x_2542_, v___x_2541_);
return v___x_2543_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__54(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2550_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__53));
v___x_2551_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__51, &l_Lake_LeanConfig___fields___closed__51_once, _init_l_Lake_LeanConfig___fields___closed__51);
v___x_2552_ = lean_array_push(v___x_2551_, v___x_2550_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__54, &l_Lake_LeanConfig___fields___closed__54_once, _init_l_Lake_LeanConfig___fields___closed__54);
return v___x_2553_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lake_LeanConfig___fields;
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2555_, lean_object* v_x2_2556_){
_start:
{
lean_object* v_name_2557_; lean_object* v___x_2558_; 
v_name_2557_ = lean_ctor_get(v_x2_2556_, 0);
lean_inc(v_name_2557_);
v___x_2558_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2557_, v_x2_2556_, v_x1_2555_);
return v___x_2558_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = l_Lake_LeanConfig___fields;
v___x_2560_ = lean_array_get_size(v___x_2559_);
return v___x_2560_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; uint8_t v___x_2582_; 
v___x_2580_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2581_ = lean_unsigned_to_nat(0u);
v___x_2582_ = lean_nat_dec_lt(v___x_2581_, v___x_2580_);
return v___x_2582_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2583_ = lean_unsigned_to_nat(0u);
v___x_2584_ = lean_box(1);
v___x_2585_ = l_Lake_LeanConfig___fields;
v___x_2586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___x_2584_);
lean_ctor_set(v___x_2586_, 2, v___x_2583_);
return v___x_2586_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2588_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2589_ = lean_nat_dec_le(v___x_2588_, v___x_2588_);
return v___x_2589_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2590_; size_t v___x_2591_; 
v___x_2590_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2591_ = lean_usize_of_nat(v___x_2590_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2592_; size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2592_ = lean_box(1);
v___x_2593_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l_Lake_LeanConfig___fields;
v___f_2596_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2597_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2597_, v___f_2596_, v___x_2595_, v___x_2594_, v___x_2593_, v___x_2592_);
return v___x_2598_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2599_ = lean_unsigned_to_nat(0u);
v___x_2600_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2601_ = l_Lake_LeanConfig___fields;
v___x_2602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
lean_ctor_set(v___x_2602_, 1, v___x_2600_);
lean_ctor_set(v___x_2602_, 2, v___x_2599_);
return v___x_2602_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2603_; 
v___x_2603_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2604_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2605_ == 0)
{
if (v___x_2603_ == 0)
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2606_;
}
else
{
lean_object* v___x_2607_; 
v___x_2607_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2607_;
}
}
else
{
lean_object* v___x_2608_; 
v___x_2608_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2608_;
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

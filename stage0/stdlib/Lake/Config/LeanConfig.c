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
LEAN_EXPORT lean_object* l_Lake_Backend_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_Backend_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_BuildType_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_BuildType_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Backend_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lake_Backend_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lake_Backend_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lake_Backend_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lake_Backend_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg(lean_object* v_c_28_){
_start:
{
lean_inc(v_c_28_);
return v_c_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___redArg___boxed(lean_object* v_c_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lake_Backend_c_elim___redArg(v_c_29_);
lean_dec(v_c_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_c_34_){
_start:
{
lean_inc(v_c_34_);
return v_c_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_c_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_c_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lake_Backend_c_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_c_38_);
lean_dec(v_c_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg(lean_object* v_llvm_41_){
_start:
{
lean_inc(v_llvm_41_);
return v_llvm_41_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___redArg___boxed(lean_object* v_llvm_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lake_Backend_llvm_elim___redArg(v_llvm_42_);
lean_dec(v_llvm_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_llvm_47_){
_start:
{
lean_inc(v_llvm_47_);
return v_llvm_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_llvm_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_llvm_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lake_Backend_llvm_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_llvm_51_);
lean_dec(v_llvm_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg(lean_object* v_default_54_){
_start:
{
lean_inc(v_default_54_);
return v_default_54_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___redArg___boxed(lean_object* v_default_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_Backend_default_elim___redArg(v_default_55_);
lean_dec(v_default_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_default_60_){
_start:
{
lean_inc(v_default_60_);
return v_default_60_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_default_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_default_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lake_Backend_default_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_default_64_);
lean_dec(v_default_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lake_instReprBackend_repr___closed__7(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr(uint8_t v_x_80_, lean_object* v_prec_81_){
_start:
{
lean_object* v___y_83_; lean_object* v___y_90_; lean_object* v___y_97_; 
switch(v_x_80_)
{
case 0:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = lean_unsigned_to_nat(1024u);
v___x_104_ = lean_nat_dec_le(v___x_103_, v_prec_81_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_83_ = v___x_105_;
goto v___jp_82_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_83_ = v___x_106_;
goto v___jp_82_;
}
}
case 1:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_unsigned_to_nat(1024u);
v___x_108_ = lean_nat_dec_le(v___x_107_, v_prec_81_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_90_ = v___x_109_;
goto v___jp_89_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_90_ = v___x_110_;
goto v___jp_89_;
}
}
default: 
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(1024u);
v___x_112_ = lean_nat_dec_le(v___x_111_, v_prec_81_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_97_ = v___x_113_;
goto v___jp_96_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_97_ = v___x_114_;
goto v___jp_96_;
}
}
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__1));
lean_inc(v___y_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___y_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = 0;
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_86_);
v___x_88_ = l_Repr_addAppParen(v___x_87_, v_prec_81_);
return v___x_88_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_91_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__3));
lean_inc(v___y_90_);
v___x_92_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_92_, 0, v___y_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = 0;
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_92_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_93_);
v___x_95_ = l_Repr_addAppParen(v___x_94_, v_prec_81_);
return v___x_95_;
}
v___jp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_98_ = ((lean_object*)(l_Lake_instReprBackend_repr___closed__5));
lean_inc(v___y_97_);
v___x_99_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_99_, 0, v___y_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = 0;
v___x_101_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_101_, sizeof(void*)*1, v___x_100_);
v___x_102_ = l_Repr_addAppParen(v___x_101_, v_prec_81_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBackend_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_177__boxed_117_; lean_object* v_res_118_; 
v_x_177__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lake_instReprBackend_repr(v_x_177__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
LEAN_EXPORT uint8_t l_Lake_Backend_ofNat(lean_object* v_n_121_){
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
LEAN_EXPORT lean_object* l_Lake_Backend_ofNat___boxed(lean_object* v_n_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lake_Backend_ofNat(v_n_129_);
lean_dec(v_n_129_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBackend(uint8_t v_x_132_, uint8_t v_y_133_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_134_ = l_Lake_Backend_ctorIdx(v_x_132_);
v___x_135_ = l_Lake_Backend_ctorIdx(v_y_133_);
v___x_136_ = lean_nat_dec_eq(v___x_134_, v___x_135_);
lean_dec(v___x_135_);
lean_dec(v___x_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBackend___boxed(lean_object* v_x_137_, lean_object* v_y_138_){
_start:
{
uint8_t v_x_13__boxed_139_; uint8_t v_y_14__boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_x_13__boxed_139_ = lean_unbox(v_x_137_);
v_y_14__boxed_140_ = lean_unbox(v_y_138_);
v_res_141_ = l_Lake_instDecidableEqBackend(v_x_13__boxed_139_, v_y_14__boxed_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
static uint8_t _init_l_Lake_Backend_instInhabited(void){
_start:
{
uint8_t v___x_143_; 
v___x_143_ = 2;
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f(lean_object* v_s_156_){
_start:
{
lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
v___x_158_ = lean_string_dec_eq(v_s_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
v___x_160_ = lean_string_dec_eq(v_s_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
v___x_162_ = lean_string_dec_eq(v_s_156_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; 
v___x_163_ = lean_box(0);
return v___x_163_;
}
else
{
lean_object* v___x_164_; 
v___x_164_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__3));
return v___x_164_;
}
}
else
{
lean_object* v___x_165_; 
v___x_165_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__4));
return v___x_165_;
}
}
else
{
lean_object* v___x_166_; 
v___x_166_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__5));
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_ofString_x3f___boxed(lean_object* v_s_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lake_Backend_ofString_x3f(v_s_167_);
lean_dec_ref(v_s_167_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_toString(uint8_t v_bt_169_){
_start:
{
switch(v_bt_169_)
{
case 0:
{
lean_object* v___x_170_; 
v___x_170_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__0));
return v___x_170_;
}
case 1:
{
lean_object* v___x_171_; 
v___x_171_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__1));
return v___x_171_;
}
default: 
{
lean_object* v___x_172_; 
v___x_172_ = ((lean_object*)(l_Lake_Backend_ofString_x3f___closed__2));
return v___x_172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_toString___boxed(lean_object* v_bt_173_){
_start:
{
uint8_t v_bt_boxed_174_; lean_object* v_res_175_; 
v_bt_boxed_174_ = lean_unbox(v_bt_173_);
v_res_175_ = l_Lake_Backend_toString(v_bt_boxed_174_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t l_Lake_Backend_orPreferLeft(uint8_t v_x_178_, uint8_t v_x_179_){
_start:
{
if (v_x_178_ == 2)
{
return v_x_179_;
}
else
{
return v_x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_orPreferLeft___boxed(lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
uint8_t v_x_16__boxed_182_; uint8_t v_x_17__boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_x_16__boxed_182_ = lean_unbox(v_x_180_);
v_x_17__boxed_183_ = lean_unbox(v_x_181_);
v_res_184_ = l_Lake_Backend_orPreferLeft(v_x_16__boxed_182_, v_x_17__boxed_183_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx(uint8_t v_x_186_){
_start:
{
switch(v_x_186_)
{
case 0:
{
lean_object* v___x_187_; 
v___x_187_ = lean_unsigned_to_nat(0u);
return v___x_187_;
}
case 1:
{
lean_object* v___x_188_; 
v___x_188_ = lean_unsigned_to_nat(1u);
return v___x_188_;
}
case 2:
{
lean_object* v___x_189_; 
v___x_189_ = lean_unsigned_to_nat(2u);
return v___x_189_;
}
default: 
{
lean_object* v___x_190_; 
v___x_190_ = lean_unsigned_to_nat(3u);
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorIdx___boxed(lean_object* v_x_191_){
_start:
{
uint8_t v_x_boxed_192_; lean_object* v_res_193_; 
v_x_boxed_192_ = lean_unbox(v_x_191_);
v_res_193_ = l_Lake_BuildType_ctorIdx(v_x_boxed_192_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toCtorIdx(uint8_t v_x_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lake_BuildType_ctorIdx(v_x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toCtorIdx___boxed(lean_object* v_x_196_){
_start:
{
uint8_t v_x_4__boxed_197_; lean_object* v_res_198_; 
v_x_4__boxed_197_ = lean_unbox(v_x_196_);
v_res_198_ = l_Lake_BuildType_toCtorIdx(v_x_4__boxed_197_);
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
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim(lean_object* v_motive_202_, lean_object* v_ctorIdx_203_, uint8_t v_t_204_, lean_object* v_h_205_, lean_object* v_k_206_){
_start:
{
lean_inc(v_k_206_);
return v_k_206_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ctorElim___boxed(lean_object* v_motive_207_, lean_object* v_ctorIdx_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_k_211_){
_start:
{
uint8_t v_t_boxed_212_; lean_object* v_res_213_; 
v_t_boxed_212_ = lean_unbox(v_t_209_);
v_res_213_ = l_Lake_BuildType_ctorElim(v_motive_207_, v_ctorIdx_208_, v_t_boxed_212_, v_h_210_, v_k_211_);
lean_dec(v_k_211_);
lean_dec(v_ctorIdx_208_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg(lean_object* v_debug_214_){
_start:
{
lean_inc(v_debug_214_);
return v_debug_214_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___redArg___boxed(lean_object* v_debug_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lake_BuildType_debug_elim___redArg(v_debug_215_);
lean_dec(v_debug_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim(lean_object* v_motive_217_, uint8_t v_t_218_, lean_object* v_h_219_, lean_object* v_debug_220_){
_start:
{
lean_inc(v_debug_220_);
return v_debug_220_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_debug_elim___boxed(lean_object* v_motive_221_, lean_object* v_t_222_, lean_object* v_h_223_, lean_object* v_debug_224_){
_start:
{
uint8_t v_t_boxed_225_; lean_object* v_res_226_; 
v_t_boxed_225_ = lean_unbox(v_t_222_);
v_res_226_ = l_Lake_BuildType_debug_elim(v_motive_221_, v_t_boxed_225_, v_h_223_, v_debug_224_);
lean_dec(v_debug_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg(lean_object* v_relWithDebInfo_227_){
_start:
{
lean_inc(v_relWithDebInfo_227_);
return v_relWithDebInfo_227_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___redArg___boxed(lean_object* v_relWithDebInfo_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lake_BuildType_relWithDebInfo_elim___redArg(v_relWithDebInfo_228_);
lean_dec(v_relWithDebInfo_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim(lean_object* v_motive_230_, uint8_t v_t_231_, lean_object* v_h_232_, lean_object* v_relWithDebInfo_233_){
_start:
{
lean_inc(v_relWithDebInfo_233_);
return v_relWithDebInfo_233_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_relWithDebInfo_elim___boxed(lean_object* v_motive_234_, lean_object* v_t_235_, lean_object* v_h_236_, lean_object* v_relWithDebInfo_237_){
_start:
{
uint8_t v_t_boxed_238_; lean_object* v_res_239_; 
v_t_boxed_238_ = lean_unbox(v_t_235_);
v_res_239_ = l_Lake_BuildType_relWithDebInfo_elim(v_motive_234_, v_t_boxed_238_, v_h_236_, v_relWithDebInfo_237_);
lean_dec(v_relWithDebInfo_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg(lean_object* v_minSizeRel_240_){
_start:
{
lean_inc(v_minSizeRel_240_);
return v_minSizeRel_240_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___redArg___boxed(lean_object* v_minSizeRel_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lake_BuildType_minSizeRel_elim___redArg(v_minSizeRel_241_);
lean_dec(v_minSizeRel_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim(lean_object* v_motive_243_, uint8_t v_t_244_, lean_object* v_h_245_, lean_object* v_minSizeRel_246_){
_start:
{
lean_inc(v_minSizeRel_246_);
return v_minSizeRel_246_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_minSizeRel_elim___boxed(lean_object* v_motive_247_, lean_object* v_t_248_, lean_object* v_h_249_, lean_object* v_minSizeRel_250_){
_start:
{
uint8_t v_t_boxed_251_; lean_object* v_res_252_; 
v_t_boxed_251_ = lean_unbox(v_t_248_);
v_res_252_ = l_Lake_BuildType_minSizeRel_elim(v_motive_247_, v_t_boxed_251_, v_h_249_, v_minSizeRel_250_);
lean_dec(v_minSizeRel_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg(lean_object* v_release_253_){
_start:
{
lean_inc(v_release_253_);
return v_release_253_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___redArg___boxed(lean_object* v_release_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lake_BuildType_release_elim___redArg(v_release_254_);
lean_dec(v_release_254_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim(lean_object* v_motive_256_, uint8_t v_t_257_, lean_object* v_h_258_, lean_object* v_release_259_){
_start:
{
lean_inc(v_release_259_);
return v_release_259_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_release_elim___boxed(lean_object* v_motive_260_, lean_object* v_t_261_, lean_object* v_h_262_, lean_object* v_release_263_){
_start:
{
uint8_t v_t_boxed_264_; lean_object* v_res_265_; 
v_t_boxed_264_ = lean_unbox(v_t_261_);
v_res_265_ = l_Lake_BuildType_release_elim(v_motive_260_, v_t_boxed_264_, v_h_262_, v_release_263_);
lean_dec(v_release_263_);
return v_res_265_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType_default(void){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = 0;
return v___x_266_;
}
}
static uint8_t _init_l_Lake_instInhabitedBuildType(void){
_start:
{
uint8_t v___x_267_; 
v___x_267_ = 0;
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr(uint8_t v_x_280_, lean_object* v_prec_281_){
_start:
{
lean_object* v___y_283_; lean_object* v___y_290_; lean_object* v___y_297_; lean_object* v___y_304_; 
switch(v_x_280_)
{
case 0:
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_unsigned_to_nat(1024u);
v___x_311_ = lean_nat_dec_le(v___x_310_, v_prec_281_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_283_ = v___x_312_;
goto v___jp_282_;
}
else
{
lean_object* v___x_313_; 
v___x_313_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_283_ = v___x_313_;
goto v___jp_282_;
}
}
case 1:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = lean_unsigned_to_nat(1024u);
v___x_315_ = lean_nat_dec_le(v___x_314_, v_prec_281_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_290_ = v___x_316_;
goto v___jp_289_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_290_ = v___x_317_;
goto v___jp_289_;
}
}
case 2:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1024u);
v___x_319_ = lean_nat_dec_le(v___x_318_, v_prec_281_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_297_ = v___x_320_;
goto v___jp_296_;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_297_ = v___x_321_;
goto v___jp_296_;
}
}
default: 
{
lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1024u);
v___x_323_ = lean_nat_dec_le(v___x_322_, v_prec_281_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__6, &l_Lake_instReprBackend_repr___closed__6_once, _init_l_Lake_instReprBackend_repr___closed__6);
v___y_304_ = v___x_324_;
goto v___jp_303_;
}
else
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Lake_instReprBackend_repr___closed__7, &l_Lake_instReprBackend_repr___closed__7_once, _init_l_Lake_instReprBackend_repr___closed__7);
v___y_304_ = v___x_325_;
goto v___jp_303_;
}
}
}
v___jp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_284_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__1));
lean_inc(v___y_283_);
v___x_285_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_285_, 0, v___y_283_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = 0;
v___x_287_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_287_, 0, v___x_285_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*1, v___x_286_);
v___x_288_ = l_Repr_addAppParen(v___x_287_, v_prec_281_);
return v___x_288_;
}
v___jp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_291_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__3));
lean_inc(v___y_290_);
v___x_292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_292_, 0, v___y_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = 0;
v___x_294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*1, v___x_293_);
v___x_295_ = l_Repr_addAppParen(v___x_294_, v_prec_281_);
return v___x_295_;
}
v___jp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_298_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__5));
lean_inc(v___y_297_);
v___x_299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_299_, 0, v___y_297_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = 0;
v___x_301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_300_);
v___x_302_ = l_Repr_addAppParen(v___x_301_, v_prec_281_);
return v___x_302_;
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_305_ = ((lean_object*)(l_Lake_instReprBuildType_repr___closed__7));
lean_inc(v___y_304_);
v___x_306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_306_, 0, v___y_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = 0;
v___x_308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_307_);
v___x_309_ = l_Repr_addAppParen(v___x_308_, v_prec_281_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprBuildType_repr___boxed(lean_object* v_x_326_, lean_object* v_prec_327_){
_start:
{
uint8_t v_x_229__boxed_328_; lean_object* v_res_329_; 
v_x_229__boxed_328_ = lean_unbox(v_x_326_);
v_res_329_ = l_Lake_instReprBuildType_repr(v_x_229__boxed_328_, v_prec_327_);
lean_dec(v_prec_327_);
return v_res_329_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_ofNat(lean_object* v_n_332_){
_start:
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_dec_le(v_n_332_, v___x_333_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; uint8_t v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(2u);
v___x_336_ = lean_nat_dec_le(v_n_332_, v___x_335_);
if (v___x_336_ == 0)
{
uint8_t v___x_337_; 
v___x_337_ = 3;
return v___x_337_;
}
else
{
uint8_t v___x_338_; 
v___x_338_ = 2;
return v___x_338_;
}
}
else
{
lean_object* v___x_339_; uint8_t v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_nat_dec_le(v_n_332_, v___x_339_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = 1;
return v___x_341_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = 0;
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofNat___boxed(lean_object* v_n_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Lake_BuildType_ofNat(v_n_343_);
lean_dec(v_n_343_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqBuildType(uint8_t v_x_346_, uint8_t v_y_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_348_ = l_Lake_BuildType_ctorIdx(v_x_346_);
v___x_349_ = l_Lake_BuildType_ctorIdx(v_y_347_);
v___x_350_ = lean_nat_dec_eq(v___x_348_, v___x_349_);
lean_dec(v___x_349_);
lean_dec(v___x_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqBuildType___boxed(lean_object* v_x_351_, lean_object* v_y_352_){
_start:
{
uint8_t v_x_13__boxed_353_; uint8_t v_y_14__boxed_354_; uint8_t v_res_355_; lean_object* v_r_356_; 
v_x_13__boxed_353_ = lean_unbox(v_x_351_);
v_y_14__boxed_354_ = lean_unbox(v_y_352_);
v_res_355_ = l_Lake_instDecidableEqBuildType(v_x_13__boxed_353_, v_y_14__boxed_354_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint8_t l_Lake_instOrdBuildType_ord(uint8_t v_x_357_, uint8_t v_y_358_){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lake_BuildType_ctorIdx(v_x_357_);
v___x_360_ = l_Lake_BuildType_ctorIdx(v_y_358_);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
uint8_t v___x_362_; 
v___x_362_ = lean_nat_dec_eq(v___x_359_, v___x_360_);
lean_dec(v___x_360_);
lean_dec(v___x_359_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = 2;
return v___x_363_;
}
else
{
uint8_t v___x_364_; 
v___x_364_ = 1;
return v___x_364_;
}
}
else
{
uint8_t v___x_365_; 
lean_dec(v___x_360_);
lean_dec(v___x_359_);
v___x_365_ = 0;
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instOrdBuildType_ord___boxed(lean_object* v_x_366_, lean_object* v_y_367_){
_start:
{
uint8_t v_x_30__boxed_368_; uint8_t v_y_31__boxed_369_; uint8_t v_res_370_; lean_object* v_r_371_; 
v_x_30__boxed_368_ = lean_unbox(v_x_366_);
v_y_31__boxed_369_ = lean_unbox(v_y_367_);
v_res_370_ = l_Lake_instOrdBuildType_ord(v_x_30__boxed_368_, v_y_31__boxed_369_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
static lean_object* _init_l_Lake_BuildType_instLT(void){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_box(0);
return v___x_374_;
}
}
static lean_object* _init_l_Lake_BuildType_instLE(void){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = lean_box(0);
return v___x_375_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_instMin___lam__0(uint8_t v_x_376_, uint8_t v_y_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = l_Lake_instOrdBuildType_ord(v_x_376_, v_y_377_);
if (v___x_378_ == 2)
{
return v_y_377_;
}
else
{
return v_x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMin___lam__0___boxed(lean_object* v_x_379_, lean_object* v_y_380_){
_start:
{
uint8_t v_x_boxed_381_; uint8_t v_y_boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_x_boxed_381_ = lean_unbox(v_x_379_);
v_y_boxed_382_ = lean_unbox(v_y_380_);
v_res_383_ = l_Lake_BuildType_instMin___lam__0(v_x_boxed_381_, v_y_boxed_382_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_Lake_BuildType_instMax___lam__0(uint8_t v_x_387_, uint8_t v_y_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = l_Lake_instOrdBuildType_ord(v_x_387_, v_y_388_);
if (v___x_389_ == 2)
{
return v_x_387_;
}
else
{
return v_y_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_instMax___lam__0___boxed(lean_object* v_x_390_, lean_object* v_y_391_){
_start:
{
uint8_t v_x_boxed_392_; uint8_t v_y_boxed_393_; uint8_t v_res_394_; lean_object* v_r_395_; 
v_x_boxed_392_ = lean_unbox(v_x_390_);
v_y_boxed_393_ = lean_unbox(v_y_391_);
v_res_394_ = l_Lake_BuildType_instMax___lam__0(v_x_boxed_392_, v_y_boxed_393_);
v_r_395_ = lean_box(v_res_394_);
return v_r_395_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs(uint8_t v_x_429_){
_start:
{
switch(v_x_429_)
{
case 0:
{
lean_object* v___x_430_; 
v___x_430_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__2));
return v___x_430_;
}
case 1:
{
lean_object* v___x_431_; 
v___x_431_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__5));
return v___x_431_;
}
case 2:
{
lean_object* v___x_432_; 
v___x_432_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__7));
return v___x_432_;
}
default: 
{
lean_object* v___x_433_; 
v___x_433_ = ((lean_object*)(l_Lake_BuildType_leancArgs___closed__8));
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leancArgs___boxed(lean_object* v_x_434_){
_start:
{
uint8_t v_x_163__boxed_435_; lean_object* v_res_436_; 
v_x_163__boxed_435_ = lean_unbox(v_x_434_);
v_res_436_ = l_Lake_BuildType_leancArgs(v_x_163__boxed_435_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_ofString_x3f(lean_object* v_s_453_){
_start:
{
lean_object* v___y_455_; lean_object* v___x_469_; uint32_t v___x_470_; uint32_t v___x_471_; uint8_t v___x_472_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = lean_string_utf8_get(v_s_453_, v___x_469_);
v___x_471_ = 65;
v___x_472_ = lean_uint32_dec_le(v___x_471_, v___x_470_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
v___x_473_ = lean_string_utf8_set(v_s_453_, v___x_469_, v___x_470_);
v___y_455_ = v___x_473_;
goto v___jp_454_;
}
else
{
uint32_t v___x_474_; uint8_t v___x_475_; 
v___x_474_ = 90;
v___x_475_ = lean_uint32_dec_le(v___x_470_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
v___x_476_ = lean_string_utf8_set(v_s_453_, v___x_469_, v___x_470_);
v___y_455_ = v___x_476_;
goto v___jp_454_;
}
else
{
uint32_t v___x_477_; uint32_t v___x_478_; lean_object* v___x_479_; 
v___x_477_ = 32;
v___x_478_ = lean_uint32_add(v___x_470_, v___x_477_);
v___x_479_ = lean_string_utf8_set(v_s_453_, v___x_469_, v___x_478_);
v___y_455_ = v___x_479_;
goto v___jp_454_;
}
}
v___jp_454_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
v___x_457_ = lean_string_dec_eq(v___y_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
v___x_459_ = lean_string_dec_eq(v___y_455_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
v___x_461_ = lean_string_dec_eq(v___y_455_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
v___x_463_ = lean_string_dec_eq(v___y_455_, v___x_462_);
lean_dec_ref(v___y_455_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_box(0);
return v___x_464_;
}
else
{
lean_object* v___x_465_; 
v___x_465_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__4));
return v___x_465_;
}
}
else
{
lean_object* v___x_466_; 
lean_dec_ref(v___y_455_);
v___x_466_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__5));
return v___x_466_;
}
}
else
{
lean_object* v___x_467_; 
lean_dec_ref(v___y_455_);
v___x_467_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__6));
return v___x_467_;
}
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v___y_455_);
v___x_468_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__7));
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString(uint8_t v_bt_480_){
_start:
{
switch(v_bt_480_)
{
case 0:
{
lean_object* v___x_481_; 
v___x_481_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__0));
return v___x_481_;
}
case 1:
{
lean_object* v___x_482_; 
v___x_482_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__1));
return v___x_482_;
}
case 2:
{
lean_object* v___x_483_; 
v___x_483_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__2));
return v___x_483_;
}
default: 
{
lean_object* v___x_484_; 
v___x_484_ = ((lean_object*)(l_Lake_BuildType_ofString_x3f___closed__3));
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_toString___boxed(lean_object* v_bt_485_){
_start:
{
uint8_t v_bt_boxed_486_; lean_object* v_res_487_; 
v_bt_boxed_486_ = lean_unbox(v_bt_485_);
v_res_487_ = l_Lake_BuildType_toString(v_bt_boxed_486_);
return v_res_487_;
}
}
static lean_object* _init_l_Lake_BuildType_leanOptions___closed__3(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_495_ = lean_box(1);
v___x_496_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__2));
v___x_497_ = ((lean_object*)(l_Lake_BuildType_leanOptions___closed__1));
v___x_498_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_497_, v___x_496_, v___x_495_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions(uint8_t v_x_499_){
_start:
{
if (v_x_499_ == 0)
{
lean_object* v___x_500_; 
v___x_500_ = lean_obj_once(&l_Lake_BuildType_leanOptions___closed__3, &l_Lake_BuildType_leanOptions___closed__3_once, _init_l_Lake_BuildType_leanOptions___closed__3);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = lean_box(1);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanOptions___boxed(lean_object* v_x_502_){
_start:
{
uint8_t v_x_70__boxed_503_; lean_object* v_res_504_; 
v_x_70__boxed_503_ = lean_unbox(v_x_502_);
v_res_504_ = l_Lake_BuildType_leanOptions(v_x_70__boxed_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs(uint8_t v_t_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_leanArgs___boxed(lean_object* v_t_509_){
_start:
{
uint8_t v_t_boxed_510_; lean_object* v_res_511_; 
v_t_boxed_510_ = lean_unbox(v_t_509_);
v_res_511_ = l_Lake_BuildType_leanArgs(v_t_boxed_510_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v___x_530_; 
v___x_530_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1));
return v___x_530_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_532_; uint8_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_val_531_ = lean_ctor_get(v_x_528_, 0);
v___x_532_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3));
v___x_533_ = lean_unbox(v_val_531_);
v___x_534_ = l_Bool_repr___redArg(v___x_533_);
v___x_535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_532_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = l_Repr_addAppParen(v___x_535_, v_x_529_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_537_, v_x_538_);
lean_dec(v_x_538_);
lean_dec(v_x_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_nat_to_int(v_a_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object* v___y_542_){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = l_String_quote(v___y_542_);
v___x_544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_547_) == 0)
{
lean_dec(v_x_545_);
return v_x_546_;
}
else
{
lean_object* v_head_548_; lean_object* v_tail_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_560_; 
v_head_548_ = lean_ctor_get(v_x_547_, 0);
v_tail_549_ = lean_ctor_get(v_x_547_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_547_);
if (v_isSharedCheck_560_ == 0)
{
v___x_551_ = v_x_547_;
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_tail_549_);
lean_inc(v_head_548_);
lean_dec(v_x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_560_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
lean_inc(v_x_545_);
if (v_isShared_552_ == 0)
{
lean_ctor_set_tag(v___x_551_, 5);
lean_ctor_set(v___x_551_, 1, v_x_545_);
lean_ctor_set(v___x_551_, 0, v_x_546_);
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_x_546_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_x_545_);
v___x_554_ = v_reuseFailAlloc_559_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_555_ = l_String_quote(v_head_548_);
v___x_556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_554_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
v_x_546_ = v___x_557_;
v_x_547_ = v_tail_549_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object* v_x_561_, lean_object* v_x_562_, lean_object* v_x_563_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_dec(v_x_561_);
return v_x_562_;
}
else
{
lean_object* v_head_564_; lean_object* v_tail_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_576_; 
v_head_564_ = lean_ctor_get(v_x_563_, 0);
v_tail_565_ = lean_ctor_get(v_x_563_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_563_);
if (v_isSharedCheck_576_ == 0)
{
v___x_567_ = v_x_563_;
v_isShared_568_ = v_isSharedCheck_576_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_tail_565_);
lean_inc(v_head_564_);
lean_dec(v_x_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_576_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_570_; 
lean_inc(v_x_561_);
if (v_isShared_568_ == 0)
{
lean_ctor_set_tag(v___x_567_, 5);
lean_ctor_set(v___x_567_, 1, v_x_561_);
lean_ctor_set(v___x_567_, 0, v_x_562_);
v___x_570_ = v___x_567_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_x_562_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v_x_561_);
v___x_570_ = v_reuseFailAlloc_575_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = l_String_quote(v_head_564_);
v___x_572_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_570_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_561_, v___x_573_, v_tail_565_);
return v___x_574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v___x_579_; 
lean_dec(v_x_578_);
v___x_579_ = lean_box(0);
return v___x_579_;
}
else
{
lean_object* v_tail_580_; 
v_tail_580_ = lean_ctor_get(v_x_577_, 1);
if (lean_obj_tag(v_tail_580_) == 0)
{
lean_object* v_head_581_; lean_object* v___x_582_; 
lean_dec(v_x_578_);
v_head_581_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_head_581_);
lean_dec_ref_known(v_x_577_, 2);
v___x_582_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_581_);
return v___x_582_;
}
else
{
lean_object* v_head_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
lean_inc(v_tail_580_);
v_head_583_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_head_583_);
lean_dec_ref_known(v_x_577_, 2);
v___x_584_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_583_);
v___x_585_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_578_, v___x_584_, v_tail_580_);
return v___x_585_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0));
v___x_595_ = lean_string_length(v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5);
v___x_597_ = lean_nat_to_int(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object* v_xs_605_){
_start:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_array_get_size(v_xs_605_);
v___x_607_ = lean_unsigned_to_nat(0u);
v___x_608_ = lean_nat_dec_eq(v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_609_ = lean_array_to_list(v_xs_605_);
v___x_610_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_611_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_609_, v___x_610_);
v___x_612_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_613_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_614_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
lean_ctor_set(v___x_614_, 1, v___x_611_);
v___x_615_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_616_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_612_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = l_Std_Format_fill(v___x_617_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; 
lean_dec_ref(v_xs_605_);
v___x_619_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object* v___y_620_){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = l_Lake_Target_repr___redArg(v___y_620_, v___x_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object* v_x_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
lean_dec(v_x_623_);
return v_x_624_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_638_; 
v_head_626_ = lean_ctor_get(v_x_625_, 0);
v_tail_627_ = lean_ctor_get(v_x_625_, 1);
v_isSharedCheck_638_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_638_ == 0)
{
v___x_629_ = v_x_625_;
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_tail_627_);
lean_inc(v_head_626_);
lean_dec(v_x_625_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_638_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
lean_inc(v_x_623_);
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 5);
lean_ctor_set(v___x_629_, 1, v_x_623_);
lean_ctor_set(v___x_629_, 0, v_x_624_);
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_x_624_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_x_623_);
v___x_632_ = v_reuseFailAlloc_637_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = l_Lake_Target_repr___redArg(v_head_626_, v___x_633_);
v___x_635_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_632_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v_x_624_ = v___x_635_;
v_x_625_ = v_tail_627_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_dec(v_x_639_);
return v_x_640_;
}
else
{
lean_object* v_head_642_; lean_object* v_tail_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_654_; 
v_head_642_ = lean_ctor_get(v_x_641_, 0);
v_tail_643_ = lean_ctor_get(v_x_641_, 1);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_654_ == 0)
{
v___x_645_ = v_x_641_;
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_tail_643_);
lean_inc(v_head_642_);
lean_dec(v_x_641_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_654_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
lean_inc(v_x_639_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 5);
lean_ctor_set(v___x_645_, 1, v_x_639_);
lean_ctor_set(v___x_645_, 0, v_x_640_);
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_x_640_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_x_639_);
v___x_648_ = v_reuseFailAlloc_653_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = l_Lake_Target_repr___redArg(v_head_642_, v___x_649_);
v___x_651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_648_);
lean_ctor_set(v___x_651_, 1, v___x_650_);
v___x_652_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_639_, v___x_651_, v_tail_643_);
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
if (lean_obj_tag(v_x_655_) == 0)
{
lean_object* v___x_657_; 
lean_dec(v_x_656_);
v___x_657_ = lean_box(0);
return v___x_657_;
}
else
{
lean_object* v_tail_658_; 
v_tail_658_ = lean_ctor_get(v_x_655_, 1);
if (lean_obj_tag(v_tail_658_) == 0)
{
lean_object* v_head_659_; lean_object* v___x_660_; 
lean_dec(v_x_656_);
v_head_659_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_head_659_);
lean_dec_ref_known(v_x_655_, 2);
v___x_660_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_659_);
return v___x_660_;
}
else
{
lean_object* v_head_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
lean_inc(v_tail_658_);
v_head_661_ = lean_ctor_get(v_x_655_, 0);
lean_inc(v_head_661_);
lean_dec_ref_known(v_x_655_, 2);
v___x_662_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_661_);
v___x_663_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_656_, v___x_662_, v_tail_658_);
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object* v_xs_664_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_665_ = lean_array_get_size(v_xs_664_);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_nat_dec_eq(v___x_665_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_668_ = lean_array_to_list(v_xs_664_);
v___x_669_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_670_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_668_, v___x_669_);
v___x_671_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_672_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v___x_670_);
v___x_674_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_671_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = l_Std_Format_fill(v___x_676_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_xs_664_);
v___x_678_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_){
_start:
{
if (lean_obj_tag(v_x_681_) == 0)
{
lean_dec(v_x_679_);
return v_x_680_;
}
else
{
lean_object* v_head_682_; lean_object* v_tail_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_693_; 
v_head_682_ = lean_ctor_get(v_x_681_, 0);
v_tail_683_ = lean_ctor_get(v_x_681_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_x_681_);
if (v_isSharedCheck_693_ == 0)
{
v___x_685_ = v_x_681_;
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_tail_683_);
lean_inc(v_head_682_);
lean_dec(v_x_681_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_693_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
lean_inc(v_x_679_);
if (v_isShared_686_ == 0)
{
lean_ctor_set_tag(v___x_685_, 5);
lean_ctor_set(v___x_685_, 1, v_x_679_);
lean_ctor_set(v___x_685_, 0, v_x_680_);
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_x_680_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_x_679_);
v___x_688_ = v_reuseFailAlloc_692_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = l_Lean_instReprLeanOption_repr___redArg(v_head_682_);
v___x_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_688_);
lean_ctor_set(v___x_690_, 1, v___x_689_);
v_x_680_ = v___x_690_;
v_x_681_ = v_tail_683_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 0)
{
lean_dec(v_x_694_);
return v_x_695_;
}
else
{
lean_object* v_head_697_; lean_object* v_tail_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_708_; 
v_head_697_ = lean_ctor_get(v_x_696_, 0);
v_tail_698_ = lean_ctor_get(v_x_696_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_x_696_);
if (v_isSharedCheck_708_ == 0)
{
v___x_700_ = v_x_696_;
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_tail_698_);
lean_inc(v_head_697_);
lean_dec(v_x_696_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_708_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
lean_inc(v_x_694_);
if (v_isShared_701_ == 0)
{
lean_ctor_set_tag(v___x_700_, 5);
lean_ctor_set(v___x_700_, 1, v_x_694_);
lean_ctor_set(v___x_700_, 0, v_x_695_);
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_x_695_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_x_694_);
v___x_703_ = v_reuseFailAlloc_707_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = l_Lean_instReprLeanOption_repr___redArg(v_head_697_);
v___x_705_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_703_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_694_, v___x_705_, v_tail_698_);
return v___x_706_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_709_) == 0)
{
lean_object* v___x_711_; 
lean_dec(v_x_710_);
v___x_711_ = lean_box(0);
return v___x_711_;
}
else
{
lean_object* v_tail_712_; 
v_tail_712_ = lean_ctor_get(v_x_709_, 1);
if (lean_obj_tag(v_tail_712_) == 0)
{
lean_object* v_head_713_; lean_object* v___x_714_; 
lean_dec(v_x_710_);
v_head_713_ = lean_ctor_get(v_x_709_, 0);
lean_inc(v_head_713_);
lean_dec_ref_known(v_x_709_, 2);
v___x_714_ = l_Lean_instReprLeanOption_repr___redArg(v_head_713_);
return v___x_714_;
}
else
{
lean_object* v_head_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_inc(v_tail_712_);
v_head_715_ = lean_ctor_get(v_x_709_, 0);
lean_inc(v_head_715_);
lean_dec_ref_known(v_x_709_, 2);
v___x_716_ = l_Lean_instReprLeanOption_repr___redArg(v_head_715_);
v___x_717_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_710_, v___x_716_, v_tail_712_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object* v_xs_718_){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_array_get_size(v_xs_718_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_nat_dec_eq(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_722_ = lean_array_to_list(v_xs_718_);
v___x_723_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_724_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_722_, v___x_723_);
v___x_725_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_726_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_727_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___x_724_);
v___x_728_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_725_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
v___x_731_ = l_Std_Format_fill(v___x_730_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; 
lean_dec_ref(v_xs_718_);
v___x_732_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_735_) == 0)
{
lean_dec(v_x_733_);
return v_x_734_;
}
else
{
lean_object* v_head_736_; lean_object* v_tail_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_748_; 
v_head_736_ = lean_ctor_get(v_x_735_, 0);
v_tail_737_ = lean_ctor_get(v_x_735_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_x_735_);
if (v_isSharedCheck_748_ == 0)
{
v___x_739_ = v_x_735_;
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_tail_737_);
lean_inc(v_head_736_);
lean_dec(v_x_735_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_748_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
lean_inc(v_x_733_);
if (v_isShared_740_ == 0)
{
lean_ctor_set_tag(v___x_739_, 5);
lean_ctor_set(v___x_739_, 1, v_x_733_);
lean_ctor_set(v___x_739_, 0, v_x_734_);
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_x_734_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_x_733_);
v___x_742_ = v_reuseFailAlloc_747_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = l_Lake_Target_repr___redArg(v_head_736_, v___x_743_);
v___x_745_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_745_, 0, v___x_742_);
lean_ctor_set(v___x_745_, 1, v___x_744_);
v_x_734_ = v___x_745_;
v_x_735_ = v_tail_737_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
if (lean_obj_tag(v_x_751_) == 0)
{
lean_dec(v_x_749_);
return v_x_750_;
}
else
{
lean_object* v_head_752_; lean_object* v_tail_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v_head_752_ = lean_ctor_get(v_x_751_, 0);
v_tail_753_ = lean_ctor_get(v_x_751_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v_x_751_);
if (v_isSharedCheck_764_ == 0)
{
v___x_755_ = v_x_751_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_tail_753_);
lean_inc(v_head_752_);
lean_dec(v_x_751_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
lean_inc(v_x_749_);
if (v_isShared_756_ == 0)
{
lean_ctor_set_tag(v___x_755_, 5);
lean_ctor_set(v___x_755_, 1, v_x_749_);
lean_ctor_set(v___x_755_, 0, v_x_750_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_x_750_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_x_749_);
v___x_758_ = v_reuseFailAlloc_763_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = l_Lake_Target_repr___redArg(v_head_752_, v___x_759_);
v___x_761_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_749_, v___x_761_, v_tail_753_);
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object* v_x_765_, lean_object* v_x_766_){
_start:
{
if (lean_obj_tag(v_x_765_) == 0)
{
lean_object* v___x_767_; 
lean_dec(v_x_766_);
v___x_767_ = lean_box(0);
return v___x_767_;
}
else
{
lean_object* v_tail_768_; 
v_tail_768_ = lean_ctor_get(v_x_765_, 1);
if (lean_obj_tag(v_tail_768_) == 0)
{
lean_object* v_head_769_; lean_object* v___x_770_; 
lean_dec(v_x_766_);
v_head_769_ = lean_ctor_get(v_x_765_, 0);
lean_inc(v_head_769_);
lean_dec_ref_known(v_x_765_, 2);
v___x_770_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_769_);
return v___x_770_;
}
else
{
lean_object* v_head_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_inc(v_tail_768_);
v_head_771_ = lean_ctor_get(v_x_765_, 0);
lean_inc(v_head_771_);
lean_dec_ref_known(v_x_765_, 2);
v___x_772_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_771_);
v___x_773_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_766_, v___x_772_, v_tail_768_);
return v___x_773_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object* v_xs_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v___x_775_ = lean_array_get_size(v_xs_774_);
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = lean_nat_dec_eq(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_778_ = lean_array_to_list(v_xs_774_);
v___x_779_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_780_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_778_, v___x_779_);
v___x_781_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_782_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_783_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v___x_780_);
v___x_784_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_785_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_786_, 0, v___x_781_);
lean_ctor_set(v___x_786_, 1, v___x_785_);
v___x_787_ = l_Std_Format_fill(v___x_786_);
return v___x_787_;
}
else
{
lean_object* v___x_788_; 
lean_dec_ref(v_xs_774_);
v___x_788_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_788_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_unsigned_to_nat(13u);
v___x_803_ = lean_nat_to_int(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_unsigned_to_nat(15u);
v___x_808_ = lean_nat_to_int(v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = lean_unsigned_to_nat(16u);
v___x_813_ = lean_nat_to_int(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_unsigned_to_nat(17u);
v___x_821_ = lean_nat_to_int(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(21u);
v___x_826_ = lean_nat_to_int(v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_unsigned_to_nat(11u);
v___x_846_ = lean_nat_to_int(v___x_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(23u);
v___x_851_ = lean_nat_to_int(v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(24u);
v___x_862_ = lean_nat_to_int(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__47(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_unsigned_to_nat(19u);
v___x_867_ = lean_nat_to_int(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_870_ = lean_string_length(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__50(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_871_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__49, &l_Lake_instReprLeanConfig_repr___redArg___closed__49_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__49);
v___x_872_ = lean_nat_to_int(v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_877_){
_start:
{
uint8_t v_buildType_878_; lean_object* v_leanOptions_879_; lean_object* v_moreLeanArgs_880_; lean_object* v_weakLeanArgs_881_; lean_object* v_moreLeancArgs_882_; lean_object* v_moreServerOptions_883_; lean_object* v_weakLeancArgs_884_; lean_object* v_moreLinkObjs_885_; lean_object* v_moreLinkLibs_886_; lean_object* v_moreLinkArgs_887_; lean_object* v_weakLinkArgs_888_; uint8_t v_backend_889_; lean_object* v_platformIndependent_890_; lean_object* v_dynlibs_891_; lean_object* v_plugins_892_; uint8_t v_requiresModuleSystem_893_; uint8_t v_allowNonModules_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_buildType_878_ = lean_ctor_get_uint8(v_x_877_, sizeof(void*)*13);
v_leanOptions_879_ = lean_ctor_get(v_x_877_, 0);
lean_inc_ref(v_leanOptions_879_);
v_moreLeanArgs_880_ = lean_ctor_get(v_x_877_, 1);
lean_inc_ref(v_moreLeanArgs_880_);
v_weakLeanArgs_881_ = lean_ctor_get(v_x_877_, 2);
lean_inc_ref(v_weakLeanArgs_881_);
v_moreLeancArgs_882_ = lean_ctor_get(v_x_877_, 3);
lean_inc_ref(v_moreLeancArgs_882_);
v_moreServerOptions_883_ = lean_ctor_get(v_x_877_, 4);
lean_inc_ref(v_moreServerOptions_883_);
v_weakLeancArgs_884_ = lean_ctor_get(v_x_877_, 5);
lean_inc_ref(v_weakLeancArgs_884_);
v_moreLinkObjs_885_ = lean_ctor_get(v_x_877_, 6);
lean_inc_ref(v_moreLinkObjs_885_);
v_moreLinkLibs_886_ = lean_ctor_get(v_x_877_, 7);
lean_inc_ref(v_moreLinkLibs_886_);
v_moreLinkArgs_887_ = lean_ctor_get(v_x_877_, 8);
lean_inc_ref(v_moreLinkArgs_887_);
v_weakLinkArgs_888_ = lean_ctor_get(v_x_877_, 9);
lean_inc_ref(v_weakLinkArgs_888_);
v_backend_889_ = lean_ctor_get_uint8(v_x_877_, sizeof(void*)*13 + 1);
v_platformIndependent_890_ = lean_ctor_get(v_x_877_, 10);
lean_inc(v_platformIndependent_890_);
v_dynlibs_891_ = lean_ctor_get(v_x_877_, 11);
lean_inc_ref(v_dynlibs_891_);
v_plugins_892_ = lean_ctor_get(v_x_877_, 12);
lean_inc_ref(v_plugins_892_);
v_requiresModuleSystem_893_ = lean_ctor_get_uint8(v_x_877_, sizeof(void*)*13 + 2);
v_allowNonModules_894_ = lean_ctor_get_uint8(v_x_877_, sizeof(void*)*13 + 3);
lean_dec_ref(v_x_877_);
v___x_895_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_896_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_897_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = l_Lake_instReprBuildType_repr(v_buildType_878_, v___x_898_);
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
v___x_912_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_879_);
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
v___x_922_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_880_);
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
v___x_931_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_881_);
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
v___x_941_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_882_);
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
v___x_951_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_883_);
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
v___x_960_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_884_);
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
v___x_969_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_885_);
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
v___x_978_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_886_);
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
v___x_987_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_887_);
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
v___x_996_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_888_);
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
v___x_1006_ = l_Lake_instReprBackend_repr(v_backend_889_, v___x_898_);
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
v___x_1016_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_890_, v___x_898_);
lean_dec(v_platformIndependent_890_);
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
v___x_1025_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_891_);
v___x_1026_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1005_);
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
v___x_1034_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_892_);
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
v___x_1043_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__44, &l_Lake_instReprLeanConfig_repr___redArg___closed__44_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44);
v___x_1044_ = l_Bool_repr___redArg(v_requiresModuleSystem_893_);
v___x_1045_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*1, v___x_901_);
v___x_1047_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1042_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___x_904_);
v___x_1049_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_906_);
v___x_1050_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__46));
v___x_1051_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v___x_895_);
v___x_1053_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__47, &l_Lake_instReprLeanConfig_repr___redArg___closed__47_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__47);
v___x_1054_ = l_Bool_repr___redArg(v_allowNonModules_894_);
v___x_1055_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
lean_ctor_set_uint8(v___x_1056_, sizeof(void*)*1, v___x_901_);
v___x_1057_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1052_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__50, &l_Lake_instReprLeanConfig_repr___redArg___closed__50_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__50);
v___x_1059_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__51));
v___x_1060_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___x_1057_);
v___x_1061_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__52));
v___x_1062_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1058_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set_uint8(v___x_1064_, sizeof(void*)*1, v___x_901_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1065_, lean_object* v_prec_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1065_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1068_, lean_object* v_prec_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lake_instReprLeanConfig_repr(v_x_1068_, v_prec_1069_);
lean_dec(v_prec_1069_);
return v_res_1070_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1073_){
_start:
{
uint8_t v_buildType_1074_; 
v_buildType_1074_ = lean_ctor_get_uint8(v_cfg_1073_, sizeof(void*)*13);
return v_buildType_1074_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1075_){
_start:
{
uint8_t v_res_1076_; lean_object* v_r_1077_; 
v_res_1076_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1075_);
lean_dec_ref(v_cfg_1075_);
v_r_1077_ = lean_box(v_res_1076_);
return v_r_1077_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1078_, lean_object* v_cfg_1079_){
_start:
{
lean_object* v_leanOptions_1080_; lean_object* v_moreLeanArgs_1081_; lean_object* v_weakLeanArgs_1082_; lean_object* v_moreLeancArgs_1083_; lean_object* v_moreServerOptions_1084_; lean_object* v_weakLeancArgs_1085_; lean_object* v_moreLinkObjs_1086_; lean_object* v_moreLinkLibs_1087_; lean_object* v_moreLinkArgs_1088_; lean_object* v_weakLinkArgs_1089_; uint8_t v_backend_1090_; lean_object* v_platformIndependent_1091_; lean_object* v_dynlibs_1092_; lean_object* v_plugins_1093_; uint8_t v_requiresModuleSystem_1094_; uint8_t v_allowNonModules_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_leanOptions_1080_ = lean_ctor_get(v_cfg_1079_, 0);
v_moreLeanArgs_1081_ = lean_ctor_get(v_cfg_1079_, 1);
v_weakLeanArgs_1082_ = lean_ctor_get(v_cfg_1079_, 2);
v_moreLeancArgs_1083_ = lean_ctor_get(v_cfg_1079_, 3);
v_moreServerOptions_1084_ = lean_ctor_get(v_cfg_1079_, 4);
v_weakLeancArgs_1085_ = lean_ctor_get(v_cfg_1079_, 5);
v_moreLinkObjs_1086_ = lean_ctor_get(v_cfg_1079_, 6);
v_moreLinkLibs_1087_ = lean_ctor_get(v_cfg_1079_, 7);
v_moreLinkArgs_1088_ = lean_ctor_get(v_cfg_1079_, 8);
v_weakLinkArgs_1089_ = lean_ctor_get(v_cfg_1079_, 9);
v_backend_1090_ = lean_ctor_get_uint8(v_cfg_1079_, sizeof(void*)*13 + 1);
v_platformIndependent_1091_ = lean_ctor_get(v_cfg_1079_, 10);
v_dynlibs_1092_ = lean_ctor_get(v_cfg_1079_, 11);
v_plugins_1093_ = lean_ctor_get(v_cfg_1079_, 12);
v_requiresModuleSystem_1094_ = lean_ctor_get_uint8(v_cfg_1079_, sizeof(void*)*13 + 2);
v_allowNonModules_1095_ = lean_ctor_get_uint8(v_cfg_1079_, sizeof(void*)*13 + 3);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_cfg_1079_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v_cfg_1079_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_plugins_1093_);
lean_inc(v_dynlibs_1092_);
lean_inc(v_platformIndependent_1091_);
lean_inc(v_weakLinkArgs_1089_);
lean_inc(v_moreLinkArgs_1088_);
lean_inc(v_moreLinkLibs_1087_);
lean_inc(v_moreLinkObjs_1086_);
lean_inc(v_weakLeancArgs_1085_);
lean_inc(v_moreServerOptions_1084_);
lean_inc(v_moreLeancArgs_1083_);
lean_inc(v_weakLeanArgs_1082_);
lean_inc(v_moreLeanArgs_1081_);
lean_inc(v_leanOptions_1080_);
lean_dec(v_cfg_1079_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_leanOptions_1080_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_moreLeanArgs_1081_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_weakLeanArgs_1082_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_moreLeancArgs_1083_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_moreServerOptions_1084_);
lean_ctor_set(v_reuseFailAlloc_1101_, 5, v_weakLeancArgs_1085_);
lean_ctor_set(v_reuseFailAlloc_1101_, 6, v_moreLinkObjs_1086_);
lean_ctor_set(v_reuseFailAlloc_1101_, 7, v_moreLinkLibs_1087_);
lean_ctor_set(v_reuseFailAlloc_1101_, 8, v_moreLinkArgs_1088_);
lean_ctor_set(v_reuseFailAlloc_1101_, 9, v_weakLinkArgs_1089_);
lean_ctor_set(v_reuseFailAlloc_1101_, 10, v_platformIndependent_1091_);
lean_ctor_set(v_reuseFailAlloc_1101_, 11, v_dynlibs_1092_);
lean_ctor_set(v_reuseFailAlloc_1101_, 12, v_plugins_1093_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*13 + 1, v_backend_1090_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1094_);
lean_ctor_set_uint8(v_reuseFailAlloc_1101_, sizeof(void*)*13 + 3, v_allowNonModules_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_ctor_set_uint8(v___x_1100_, sizeof(void*)*13, v_val_1078_);
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1103_, lean_object* v_cfg_1104_){
_start:
{
uint8_t v_val_85__boxed_1105_; lean_object* v_res_1106_; 
v_val_85__boxed_1105_ = lean_unbox(v_val_1103_);
v_res_1106_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_85__boxed_1105_, v_cfg_1104_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1107_, lean_object* v_cfg_1108_){
_start:
{
uint8_t v_buildType_1109_; lean_object* v_leanOptions_1110_; lean_object* v_moreLeanArgs_1111_; lean_object* v_weakLeanArgs_1112_; lean_object* v_moreLeancArgs_1113_; lean_object* v_moreServerOptions_1114_; lean_object* v_weakLeancArgs_1115_; lean_object* v_moreLinkObjs_1116_; lean_object* v_moreLinkLibs_1117_; lean_object* v_moreLinkArgs_1118_; lean_object* v_weakLinkArgs_1119_; uint8_t v_backend_1120_; lean_object* v_platformIndependent_1121_; lean_object* v_dynlibs_1122_; lean_object* v_plugins_1123_; uint8_t v_requiresModuleSystem_1124_; uint8_t v_allowNonModules_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1135_; 
v_buildType_1109_ = lean_ctor_get_uint8(v_cfg_1108_, sizeof(void*)*13);
v_leanOptions_1110_ = lean_ctor_get(v_cfg_1108_, 0);
v_moreLeanArgs_1111_ = lean_ctor_get(v_cfg_1108_, 1);
v_weakLeanArgs_1112_ = lean_ctor_get(v_cfg_1108_, 2);
v_moreLeancArgs_1113_ = lean_ctor_get(v_cfg_1108_, 3);
v_moreServerOptions_1114_ = lean_ctor_get(v_cfg_1108_, 4);
v_weakLeancArgs_1115_ = lean_ctor_get(v_cfg_1108_, 5);
v_moreLinkObjs_1116_ = lean_ctor_get(v_cfg_1108_, 6);
v_moreLinkLibs_1117_ = lean_ctor_get(v_cfg_1108_, 7);
v_moreLinkArgs_1118_ = lean_ctor_get(v_cfg_1108_, 8);
v_weakLinkArgs_1119_ = lean_ctor_get(v_cfg_1108_, 9);
v_backend_1120_ = lean_ctor_get_uint8(v_cfg_1108_, sizeof(void*)*13 + 1);
v_platformIndependent_1121_ = lean_ctor_get(v_cfg_1108_, 10);
v_dynlibs_1122_ = lean_ctor_get(v_cfg_1108_, 11);
v_plugins_1123_ = lean_ctor_get(v_cfg_1108_, 12);
v_requiresModuleSystem_1124_ = lean_ctor_get_uint8(v_cfg_1108_, sizeof(void*)*13 + 2);
v_allowNonModules_1125_ = lean_ctor_get_uint8(v_cfg_1108_, sizeof(void*)*13 + 3);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_cfg_1108_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1127_ = v_cfg_1108_;
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_plugins_1123_);
lean_inc(v_dynlibs_1122_);
lean_inc(v_platformIndependent_1121_);
lean_inc(v_weakLinkArgs_1119_);
lean_inc(v_moreLinkArgs_1118_);
lean_inc(v_moreLinkLibs_1117_);
lean_inc(v_moreLinkObjs_1116_);
lean_inc(v_weakLeancArgs_1115_);
lean_inc(v_moreServerOptions_1114_);
lean_inc(v_moreLeancArgs_1113_);
lean_inc(v_weakLeanArgs_1112_);
lean_inc(v_moreLeanArgs_1111_);
lean_inc(v_leanOptions_1110_);
lean_dec(v_cfg_1108_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1135_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1129_ = lean_box(v_buildType_1109_);
v___x_1130_ = lean_apply_1(v_f_1107_, v___x_1129_);
if (v_isShared_1128_ == 0)
{
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_leanOptions_1110_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_moreLeanArgs_1111_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_weakLeanArgs_1112_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_moreLeancArgs_1113_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_moreServerOptions_1114_);
lean_ctor_set(v_reuseFailAlloc_1134_, 5, v_weakLeancArgs_1115_);
lean_ctor_set(v_reuseFailAlloc_1134_, 6, v_moreLinkObjs_1116_);
lean_ctor_set(v_reuseFailAlloc_1134_, 7, v_moreLinkLibs_1117_);
lean_ctor_set(v_reuseFailAlloc_1134_, 8, v_moreLinkArgs_1118_);
lean_ctor_set(v_reuseFailAlloc_1134_, 9, v_weakLinkArgs_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 10, v_platformIndependent_1121_);
lean_ctor_set(v_reuseFailAlloc_1134_, 11, v_dynlibs_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 12, v_plugins_1123_);
v___x_1132_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_unbox(v___x_1130_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*13, v___x_1133_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*13 + 1, v_backend_1120_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1124_);
lean_ctor_set_uint8(v___x_1132_, sizeof(void*)*13 + 3, v_allowNonModules_1125_);
return v___x_1132_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1136_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = 3;
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1138_){
_start:
{
uint8_t v_res_1139_; lean_object* v_r_1140_; 
v_res_1139_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1138_);
lean_dec_ref(v_x_1138_);
v_r_1140_ = lean_box(v_res_1139_);
return v_r_1140_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1152_){
_start:
{
lean_object* v_leanOptions_1153_; 
v_leanOptions_1153_ = lean_ctor_get(v_cfg_1152_, 0);
lean_inc_ref(v_leanOptions_1153_);
return v_leanOptions_1153_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1154_);
lean_dec_ref(v_cfg_1154_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1156_, lean_object* v_cfg_1157_){
_start:
{
uint8_t v_buildType_1158_; lean_object* v_moreLeanArgs_1159_; lean_object* v_weakLeanArgs_1160_; lean_object* v_moreLeancArgs_1161_; lean_object* v_moreServerOptions_1162_; lean_object* v_weakLeancArgs_1163_; lean_object* v_moreLinkObjs_1164_; lean_object* v_moreLinkLibs_1165_; lean_object* v_moreLinkArgs_1166_; lean_object* v_weakLinkArgs_1167_; uint8_t v_backend_1168_; lean_object* v_platformIndependent_1169_; lean_object* v_dynlibs_1170_; lean_object* v_plugins_1171_; uint8_t v_requiresModuleSystem_1172_; uint8_t v_allowNonModules_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
v_buildType_1158_ = lean_ctor_get_uint8(v_cfg_1157_, sizeof(void*)*13);
v_moreLeanArgs_1159_ = lean_ctor_get(v_cfg_1157_, 1);
v_weakLeanArgs_1160_ = lean_ctor_get(v_cfg_1157_, 2);
v_moreLeancArgs_1161_ = lean_ctor_get(v_cfg_1157_, 3);
v_moreServerOptions_1162_ = lean_ctor_get(v_cfg_1157_, 4);
v_weakLeancArgs_1163_ = lean_ctor_get(v_cfg_1157_, 5);
v_moreLinkObjs_1164_ = lean_ctor_get(v_cfg_1157_, 6);
v_moreLinkLibs_1165_ = lean_ctor_get(v_cfg_1157_, 7);
v_moreLinkArgs_1166_ = lean_ctor_get(v_cfg_1157_, 8);
v_weakLinkArgs_1167_ = lean_ctor_get(v_cfg_1157_, 9);
v_backend_1168_ = lean_ctor_get_uint8(v_cfg_1157_, sizeof(void*)*13 + 1);
v_platformIndependent_1169_ = lean_ctor_get(v_cfg_1157_, 10);
v_dynlibs_1170_ = lean_ctor_get(v_cfg_1157_, 11);
v_plugins_1171_ = lean_ctor_get(v_cfg_1157_, 12);
v_requiresModuleSystem_1172_ = lean_ctor_get_uint8(v_cfg_1157_, sizeof(void*)*13 + 2);
v_allowNonModules_1173_ = lean_ctor_get_uint8(v_cfg_1157_, sizeof(void*)*13 + 3);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_cfg_1157_);
if (v_isSharedCheck_1180_ == 0)
{
lean_object* v_unused_1181_; 
v_unused_1181_ = lean_ctor_get(v_cfg_1157_, 0);
lean_dec(v_unused_1181_);
v___x_1175_ = v_cfg_1157_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_plugins_1171_);
lean_inc(v_dynlibs_1170_);
lean_inc(v_platformIndependent_1169_);
lean_inc(v_weakLinkArgs_1167_);
lean_inc(v_moreLinkArgs_1166_);
lean_inc(v_moreLinkLibs_1165_);
lean_inc(v_moreLinkObjs_1164_);
lean_inc(v_weakLeancArgs_1163_);
lean_inc(v_moreServerOptions_1162_);
lean_inc(v_moreLeancArgs_1161_);
lean_inc(v_weakLeanArgs_1160_);
lean_inc(v_moreLeanArgs_1159_);
lean_dec(v_cfg_1157_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v_val_1156_);
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_val_1156_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v_moreLeanArgs_1159_);
lean_ctor_set(v_reuseFailAlloc_1179_, 2, v_weakLeanArgs_1160_);
lean_ctor_set(v_reuseFailAlloc_1179_, 3, v_moreLeancArgs_1161_);
lean_ctor_set(v_reuseFailAlloc_1179_, 4, v_moreServerOptions_1162_);
lean_ctor_set(v_reuseFailAlloc_1179_, 5, v_weakLeancArgs_1163_);
lean_ctor_set(v_reuseFailAlloc_1179_, 6, v_moreLinkObjs_1164_);
lean_ctor_set(v_reuseFailAlloc_1179_, 7, v_moreLinkLibs_1165_);
lean_ctor_set(v_reuseFailAlloc_1179_, 8, v_moreLinkArgs_1166_);
lean_ctor_set(v_reuseFailAlloc_1179_, 9, v_weakLinkArgs_1167_);
lean_ctor_set(v_reuseFailAlloc_1179_, 10, v_platformIndependent_1169_);
lean_ctor_set(v_reuseFailAlloc_1179_, 11, v_dynlibs_1170_);
lean_ctor_set(v_reuseFailAlloc_1179_, 12, v_plugins_1171_);
lean_ctor_set_uint8(v_reuseFailAlloc_1179_, sizeof(void*)*13, v_buildType_1158_);
lean_ctor_set_uint8(v_reuseFailAlloc_1179_, sizeof(void*)*13 + 1, v_backend_1168_);
lean_ctor_set_uint8(v_reuseFailAlloc_1179_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1172_);
lean_ctor_set_uint8(v_reuseFailAlloc_1179_, sizeof(void*)*13 + 3, v_allowNonModules_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1182_, lean_object* v_cfg_1183_){
_start:
{
uint8_t v_buildType_1184_; lean_object* v_leanOptions_1185_; lean_object* v_moreLeanArgs_1186_; lean_object* v_weakLeanArgs_1187_; lean_object* v_moreLeancArgs_1188_; lean_object* v_moreServerOptions_1189_; lean_object* v_weakLeancArgs_1190_; lean_object* v_moreLinkObjs_1191_; lean_object* v_moreLinkLibs_1192_; lean_object* v_moreLinkArgs_1193_; lean_object* v_weakLinkArgs_1194_; uint8_t v_backend_1195_; lean_object* v_platformIndependent_1196_; lean_object* v_dynlibs_1197_; lean_object* v_plugins_1198_; uint8_t v_requiresModuleSystem_1199_; uint8_t v_allowNonModules_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_buildType_1184_ = lean_ctor_get_uint8(v_cfg_1183_, sizeof(void*)*13);
v_leanOptions_1185_ = lean_ctor_get(v_cfg_1183_, 0);
v_moreLeanArgs_1186_ = lean_ctor_get(v_cfg_1183_, 1);
v_weakLeanArgs_1187_ = lean_ctor_get(v_cfg_1183_, 2);
v_moreLeancArgs_1188_ = lean_ctor_get(v_cfg_1183_, 3);
v_moreServerOptions_1189_ = lean_ctor_get(v_cfg_1183_, 4);
v_weakLeancArgs_1190_ = lean_ctor_get(v_cfg_1183_, 5);
v_moreLinkObjs_1191_ = lean_ctor_get(v_cfg_1183_, 6);
v_moreLinkLibs_1192_ = lean_ctor_get(v_cfg_1183_, 7);
v_moreLinkArgs_1193_ = lean_ctor_get(v_cfg_1183_, 8);
v_weakLinkArgs_1194_ = lean_ctor_get(v_cfg_1183_, 9);
v_backend_1195_ = lean_ctor_get_uint8(v_cfg_1183_, sizeof(void*)*13 + 1);
v_platformIndependent_1196_ = lean_ctor_get(v_cfg_1183_, 10);
v_dynlibs_1197_ = lean_ctor_get(v_cfg_1183_, 11);
v_plugins_1198_ = lean_ctor_get(v_cfg_1183_, 12);
v_requiresModuleSystem_1199_ = lean_ctor_get_uint8(v_cfg_1183_, sizeof(void*)*13 + 2);
v_allowNonModules_1200_ = lean_ctor_get_uint8(v_cfg_1183_, sizeof(void*)*13 + 3);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_cfg_1183_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1202_ = v_cfg_1183_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_plugins_1198_);
lean_inc(v_dynlibs_1197_);
lean_inc(v_platformIndependent_1196_);
lean_inc(v_weakLinkArgs_1194_);
lean_inc(v_moreLinkArgs_1193_);
lean_inc(v_moreLinkLibs_1192_);
lean_inc(v_moreLinkObjs_1191_);
lean_inc(v_weakLeancArgs_1190_);
lean_inc(v_moreServerOptions_1189_);
lean_inc(v_moreLeancArgs_1188_);
lean_inc(v_weakLeanArgs_1187_);
lean_inc(v_moreLeanArgs_1186_);
lean_inc(v_leanOptions_1185_);
lean_dec(v_cfg_1183_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_apply_1(v_f_1182_, v_leanOptions_1185_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_moreLeanArgs_1186_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_weakLeanArgs_1187_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_moreLeancArgs_1188_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_moreServerOptions_1189_);
lean_ctor_set(v_reuseFailAlloc_1207_, 5, v_weakLeancArgs_1190_);
lean_ctor_set(v_reuseFailAlloc_1207_, 6, v_moreLinkObjs_1191_);
lean_ctor_set(v_reuseFailAlloc_1207_, 7, v_moreLinkLibs_1192_);
lean_ctor_set(v_reuseFailAlloc_1207_, 8, v_moreLinkArgs_1193_);
lean_ctor_set(v_reuseFailAlloc_1207_, 9, v_weakLinkArgs_1194_);
lean_ctor_set(v_reuseFailAlloc_1207_, 10, v_platformIndependent_1196_);
lean_ctor_set(v_reuseFailAlloc_1207_, 11, v_dynlibs_1197_);
lean_ctor_set(v_reuseFailAlloc_1207_, 12, v_plugins_1198_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*13, v_buildType_1184_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*13 + 1, v_backend_1195_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1207_, sizeof(void*)*13 + 3, v_allowNonModules_1200_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1211_);
lean_dec_ref(v_x_1211_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1224_){
_start:
{
lean_object* v_moreLeanArgs_1225_; 
v_moreLeanArgs_1225_ = lean_ctor_get(v_cfg_1224_, 1);
lean_inc_ref(v_moreLeanArgs_1225_);
return v_moreLeanArgs_1225_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1226_);
lean_dec_ref(v_cfg_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1228_, lean_object* v_cfg_1229_){
_start:
{
uint8_t v_buildType_1230_; lean_object* v_leanOptions_1231_; lean_object* v_weakLeanArgs_1232_; lean_object* v_moreLeancArgs_1233_; lean_object* v_moreServerOptions_1234_; lean_object* v_weakLeancArgs_1235_; lean_object* v_moreLinkObjs_1236_; lean_object* v_moreLinkLibs_1237_; lean_object* v_moreLinkArgs_1238_; lean_object* v_weakLinkArgs_1239_; uint8_t v_backend_1240_; lean_object* v_platformIndependent_1241_; lean_object* v_dynlibs_1242_; lean_object* v_plugins_1243_; uint8_t v_requiresModuleSystem_1244_; uint8_t v_allowNonModules_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v_buildType_1230_ = lean_ctor_get_uint8(v_cfg_1229_, sizeof(void*)*13);
v_leanOptions_1231_ = lean_ctor_get(v_cfg_1229_, 0);
v_weakLeanArgs_1232_ = lean_ctor_get(v_cfg_1229_, 2);
v_moreLeancArgs_1233_ = lean_ctor_get(v_cfg_1229_, 3);
v_moreServerOptions_1234_ = lean_ctor_get(v_cfg_1229_, 4);
v_weakLeancArgs_1235_ = lean_ctor_get(v_cfg_1229_, 5);
v_moreLinkObjs_1236_ = lean_ctor_get(v_cfg_1229_, 6);
v_moreLinkLibs_1237_ = lean_ctor_get(v_cfg_1229_, 7);
v_moreLinkArgs_1238_ = lean_ctor_get(v_cfg_1229_, 8);
v_weakLinkArgs_1239_ = lean_ctor_get(v_cfg_1229_, 9);
v_backend_1240_ = lean_ctor_get_uint8(v_cfg_1229_, sizeof(void*)*13 + 1);
v_platformIndependent_1241_ = lean_ctor_get(v_cfg_1229_, 10);
v_dynlibs_1242_ = lean_ctor_get(v_cfg_1229_, 11);
v_plugins_1243_ = lean_ctor_get(v_cfg_1229_, 12);
v_requiresModuleSystem_1244_ = lean_ctor_get_uint8(v_cfg_1229_, sizeof(void*)*13 + 2);
v_allowNonModules_1245_ = lean_ctor_get_uint8(v_cfg_1229_, sizeof(void*)*13 + 3);
v_isSharedCheck_1252_ = !lean_is_exclusive(v_cfg_1229_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v_cfg_1229_, 1);
lean_dec(v_unused_1253_);
v___x_1247_ = v_cfg_1229_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_plugins_1243_);
lean_inc(v_dynlibs_1242_);
lean_inc(v_platformIndependent_1241_);
lean_inc(v_weakLinkArgs_1239_);
lean_inc(v_moreLinkArgs_1238_);
lean_inc(v_moreLinkLibs_1237_);
lean_inc(v_moreLinkObjs_1236_);
lean_inc(v_weakLeancArgs_1235_);
lean_inc(v_moreServerOptions_1234_);
lean_inc(v_moreLeancArgs_1233_);
lean_inc(v_weakLeanArgs_1232_);
lean_inc(v_leanOptions_1231_);
lean_dec(v_cfg_1229_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 1, v_val_1228_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_leanOptions_1231_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_val_1228_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_weakLeanArgs_1232_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_moreLeancArgs_1233_);
lean_ctor_set(v_reuseFailAlloc_1251_, 4, v_moreServerOptions_1234_);
lean_ctor_set(v_reuseFailAlloc_1251_, 5, v_weakLeancArgs_1235_);
lean_ctor_set(v_reuseFailAlloc_1251_, 6, v_moreLinkObjs_1236_);
lean_ctor_set(v_reuseFailAlloc_1251_, 7, v_moreLinkLibs_1237_);
lean_ctor_set(v_reuseFailAlloc_1251_, 8, v_moreLinkArgs_1238_);
lean_ctor_set(v_reuseFailAlloc_1251_, 9, v_weakLinkArgs_1239_);
lean_ctor_set(v_reuseFailAlloc_1251_, 10, v_platformIndependent_1241_);
lean_ctor_set(v_reuseFailAlloc_1251_, 11, v_dynlibs_1242_);
lean_ctor_set(v_reuseFailAlloc_1251_, 12, v_plugins_1243_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*13, v_buildType_1230_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*13 + 1, v_backend_1240_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1244_);
lean_ctor_set_uint8(v_reuseFailAlloc_1251_, sizeof(void*)*13 + 3, v_allowNonModules_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1254_, lean_object* v_cfg_1255_){
_start:
{
uint8_t v_buildType_1256_; lean_object* v_leanOptions_1257_; lean_object* v_moreLeanArgs_1258_; lean_object* v_weakLeanArgs_1259_; lean_object* v_moreLeancArgs_1260_; lean_object* v_moreServerOptions_1261_; lean_object* v_weakLeancArgs_1262_; lean_object* v_moreLinkObjs_1263_; lean_object* v_moreLinkLibs_1264_; lean_object* v_moreLinkArgs_1265_; lean_object* v_weakLinkArgs_1266_; uint8_t v_backend_1267_; lean_object* v_platformIndependent_1268_; lean_object* v_dynlibs_1269_; lean_object* v_plugins_1270_; uint8_t v_requiresModuleSystem_1271_; uint8_t v_allowNonModules_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1280_; 
v_buildType_1256_ = lean_ctor_get_uint8(v_cfg_1255_, sizeof(void*)*13);
v_leanOptions_1257_ = lean_ctor_get(v_cfg_1255_, 0);
v_moreLeanArgs_1258_ = lean_ctor_get(v_cfg_1255_, 1);
v_weakLeanArgs_1259_ = lean_ctor_get(v_cfg_1255_, 2);
v_moreLeancArgs_1260_ = lean_ctor_get(v_cfg_1255_, 3);
v_moreServerOptions_1261_ = lean_ctor_get(v_cfg_1255_, 4);
v_weakLeancArgs_1262_ = lean_ctor_get(v_cfg_1255_, 5);
v_moreLinkObjs_1263_ = lean_ctor_get(v_cfg_1255_, 6);
v_moreLinkLibs_1264_ = lean_ctor_get(v_cfg_1255_, 7);
v_moreLinkArgs_1265_ = lean_ctor_get(v_cfg_1255_, 8);
v_weakLinkArgs_1266_ = lean_ctor_get(v_cfg_1255_, 9);
v_backend_1267_ = lean_ctor_get_uint8(v_cfg_1255_, sizeof(void*)*13 + 1);
v_platformIndependent_1268_ = lean_ctor_get(v_cfg_1255_, 10);
v_dynlibs_1269_ = lean_ctor_get(v_cfg_1255_, 11);
v_plugins_1270_ = lean_ctor_get(v_cfg_1255_, 12);
v_requiresModuleSystem_1271_ = lean_ctor_get_uint8(v_cfg_1255_, sizeof(void*)*13 + 2);
v_allowNonModules_1272_ = lean_ctor_get_uint8(v_cfg_1255_, sizeof(void*)*13 + 3);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_cfg_1255_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1274_ = v_cfg_1255_;
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_plugins_1270_);
lean_inc(v_dynlibs_1269_);
lean_inc(v_platformIndependent_1268_);
lean_inc(v_weakLinkArgs_1266_);
lean_inc(v_moreLinkArgs_1265_);
lean_inc(v_moreLinkLibs_1264_);
lean_inc(v_moreLinkObjs_1263_);
lean_inc(v_weakLeancArgs_1262_);
lean_inc(v_moreServerOptions_1261_);
lean_inc(v_moreLeancArgs_1260_);
lean_inc(v_weakLeanArgs_1259_);
lean_inc(v_moreLeanArgs_1258_);
lean_inc(v_leanOptions_1257_);
lean_dec(v_cfg_1255_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1280_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1276_ = lean_apply_1(v_f_1254_, v_moreLeanArgs_1258_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v___x_1276_);
v___x_1278_ = v___x_1274_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_leanOptions_1257_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_weakLeanArgs_1259_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_moreLeancArgs_1260_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_moreServerOptions_1261_);
lean_ctor_set(v_reuseFailAlloc_1279_, 5, v_weakLeancArgs_1262_);
lean_ctor_set(v_reuseFailAlloc_1279_, 6, v_moreLinkObjs_1263_);
lean_ctor_set(v_reuseFailAlloc_1279_, 7, v_moreLinkLibs_1264_);
lean_ctor_set(v_reuseFailAlloc_1279_, 8, v_moreLinkArgs_1265_);
lean_ctor_set(v_reuseFailAlloc_1279_, 9, v_weakLinkArgs_1266_);
lean_ctor_set(v_reuseFailAlloc_1279_, 10, v_platformIndependent_1268_);
lean_ctor_set(v_reuseFailAlloc_1279_, 11, v_dynlibs_1269_);
lean_ctor_set(v_reuseFailAlloc_1279_, 12, v_plugins_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13, v_buildType_1256_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 1, v_backend_1267_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1271_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*13 + 3, v_allowNonModules_1272_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1283_);
lean_dec_ref(v_x_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1296_){
_start:
{
lean_object* v_weakLeanArgs_1297_; 
v_weakLeanArgs_1297_ = lean_ctor_get(v_cfg_1296_, 2);
lean_inc_ref(v_weakLeanArgs_1297_);
return v_weakLeanArgs_1297_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1298_);
lean_dec_ref(v_cfg_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1300_, lean_object* v_cfg_1301_){
_start:
{
uint8_t v_buildType_1302_; lean_object* v_leanOptions_1303_; lean_object* v_moreLeanArgs_1304_; lean_object* v_moreLeancArgs_1305_; lean_object* v_moreServerOptions_1306_; lean_object* v_weakLeancArgs_1307_; lean_object* v_moreLinkObjs_1308_; lean_object* v_moreLinkLibs_1309_; lean_object* v_moreLinkArgs_1310_; lean_object* v_weakLinkArgs_1311_; uint8_t v_backend_1312_; lean_object* v_platformIndependent_1313_; lean_object* v_dynlibs_1314_; lean_object* v_plugins_1315_; uint8_t v_requiresModuleSystem_1316_; uint8_t v_allowNonModules_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v_buildType_1302_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13);
v_leanOptions_1303_ = lean_ctor_get(v_cfg_1301_, 0);
v_moreLeanArgs_1304_ = lean_ctor_get(v_cfg_1301_, 1);
v_moreLeancArgs_1305_ = lean_ctor_get(v_cfg_1301_, 3);
v_moreServerOptions_1306_ = lean_ctor_get(v_cfg_1301_, 4);
v_weakLeancArgs_1307_ = lean_ctor_get(v_cfg_1301_, 5);
v_moreLinkObjs_1308_ = lean_ctor_get(v_cfg_1301_, 6);
v_moreLinkLibs_1309_ = lean_ctor_get(v_cfg_1301_, 7);
v_moreLinkArgs_1310_ = lean_ctor_get(v_cfg_1301_, 8);
v_weakLinkArgs_1311_ = lean_ctor_get(v_cfg_1301_, 9);
v_backend_1312_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13 + 1);
v_platformIndependent_1313_ = lean_ctor_get(v_cfg_1301_, 10);
v_dynlibs_1314_ = lean_ctor_get(v_cfg_1301_, 11);
v_plugins_1315_ = lean_ctor_get(v_cfg_1301_, 12);
v_requiresModuleSystem_1316_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13 + 2);
v_allowNonModules_1317_ = lean_ctor_get_uint8(v_cfg_1301_, sizeof(void*)*13 + 3);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_cfg_1301_);
if (v_isSharedCheck_1324_ == 0)
{
lean_object* v_unused_1325_; 
v_unused_1325_ = lean_ctor_get(v_cfg_1301_, 2);
lean_dec(v_unused_1325_);
v___x_1319_ = v_cfg_1301_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_plugins_1315_);
lean_inc(v_dynlibs_1314_);
lean_inc(v_platformIndependent_1313_);
lean_inc(v_weakLinkArgs_1311_);
lean_inc(v_moreLinkArgs_1310_);
lean_inc(v_moreLinkLibs_1309_);
lean_inc(v_moreLinkObjs_1308_);
lean_inc(v_weakLeancArgs_1307_);
lean_inc(v_moreServerOptions_1306_);
lean_inc(v_moreLeancArgs_1305_);
lean_inc(v_moreLeanArgs_1304_);
lean_inc(v_leanOptions_1303_);
lean_dec(v_cfg_1301_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 2, v_val_1300_);
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_leanOptions_1303_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_moreLeanArgs_1304_);
lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_val_1300_);
lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_moreLeancArgs_1305_);
lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_moreServerOptions_1306_);
lean_ctor_set(v_reuseFailAlloc_1323_, 5, v_weakLeancArgs_1307_);
lean_ctor_set(v_reuseFailAlloc_1323_, 6, v_moreLinkObjs_1308_);
lean_ctor_set(v_reuseFailAlloc_1323_, 7, v_moreLinkLibs_1309_);
lean_ctor_set(v_reuseFailAlloc_1323_, 8, v_moreLinkArgs_1310_);
lean_ctor_set(v_reuseFailAlloc_1323_, 9, v_weakLinkArgs_1311_);
lean_ctor_set(v_reuseFailAlloc_1323_, 10, v_platformIndependent_1313_);
lean_ctor_set(v_reuseFailAlloc_1323_, 11, v_dynlibs_1314_);
lean_ctor_set(v_reuseFailAlloc_1323_, 12, v_plugins_1315_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13, v_buildType_1302_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 1, v_backend_1312_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1316_);
lean_ctor_set_uint8(v_reuseFailAlloc_1323_, sizeof(void*)*13 + 3, v_allowNonModules_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1326_, lean_object* v_cfg_1327_){
_start:
{
uint8_t v_buildType_1328_; lean_object* v_leanOptions_1329_; lean_object* v_moreLeanArgs_1330_; lean_object* v_weakLeanArgs_1331_; lean_object* v_moreLeancArgs_1332_; lean_object* v_moreServerOptions_1333_; lean_object* v_weakLeancArgs_1334_; lean_object* v_moreLinkObjs_1335_; lean_object* v_moreLinkLibs_1336_; lean_object* v_moreLinkArgs_1337_; lean_object* v_weakLinkArgs_1338_; uint8_t v_backend_1339_; lean_object* v_platformIndependent_1340_; lean_object* v_dynlibs_1341_; lean_object* v_plugins_1342_; uint8_t v_requiresModuleSystem_1343_; uint8_t v_allowNonModules_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1352_; 
v_buildType_1328_ = lean_ctor_get_uint8(v_cfg_1327_, sizeof(void*)*13);
v_leanOptions_1329_ = lean_ctor_get(v_cfg_1327_, 0);
v_moreLeanArgs_1330_ = lean_ctor_get(v_cfg_1327_, 1);
v_weakLeanArgs_1331_ = lean_ctor_get(v_cfg_1327_, 2);
v_moreLeancArgs_1332_ = lean_ctor_get(v_cfg_1327_, 3);
v_moreServerOptions_1333_ = lean_ctor_get(v_cfg_1327_, 4);
v_weakLeancArgs_1334_ = lean_ctor_get(v_cfg_1327_, 5);
v_moreLinkObjs_1335_ = lean_ctor_get(v_cfg_1327_, 6);
v_moreLinkLibs_1336_ = lean_ctor_get(v_cfg_1327_, 7);
v_moreLinkArgs_1337_ = lean_ctor_get(v_cfg_1327_, 8);
v_weakLinkArgs_1338_ = lean_ctor_get(v_cfg_1327_, 9);
v_backend_1339_ = lean_ctor_get_uint8(v_cfg_1327_, sizeof(void*)*13 + 1);
v_platformIndependent_1340_ = lean_ctor_get(v_cfg_1327_, 10);
v_dynlibs_1341_ = lean_ctor_get(v_cfg_1327_, 11);
v_plugins_1342_ = lean_ctor_get(v_cfg_1327_, 12);
v_requiresModuleSystem_1343_ = lean_ctor_get_uint8(v_cfg_1327_, sizeof(void*)*13 + 2);
v_allowNonModules_1344_ = lean_ctor_get_uint8(v_cfg_1327_, sizeof(void*)*13 + 3);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_cfg_1327_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1346_ = v_cfg_1327_;
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_plugins_1342_);
lean_inc(v_dynlibs_1341_);
lean_inc(v_platformIndependent_1340_);
lean_inc(v_weakLinkArgs_1338_);
lean_inc(v_moreLinkArgs_1337_);
lean_inc(v_moreLinkLibs_1336_);
lean_inc(v_moreLinkObjs_1335_);
lean_inc(v_weakLeancArgs_1334_);
lean_inc(v_moreServerOptions_1333_);
lean_inc(v_moreLeancArgs_1332_);
lean_inc(v_weakLeanArgs_1331_);
lean_inc(v_moreLeanArgs_1330_);
lean_inc(v_leanOptions_1329_);
lean_dec(v_cfg_1327_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1352_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_apply_1(v_f_1326_, v_weakLeanArgs_1331_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 2, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_leanOptions_1329_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_moreLeanArgs_1330_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_moreLeancArgs_1332_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v_moreServerOptions_1333_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v_weakLeancArgs_1334_);
lean_ctor_set(v_reuseFailAlloc_1351_, 6, v_moreLinkObjs_1335_);
lean_ctor_set(v_reuseFailAlloc_1351_, 7, v_moreLinkLibs_1336_);
lean_ctor_set(v_reuseFailAlloc_1351_, 8, v_moreLinkArgs_1337_);
lean_ctor_set(v_reuseFailAlloc_1351_, 9, v_weakLinkArgs_1338_);
lean_ctor_set(v_reuseFailAlloc_1351_, 10, v_platformIndependent_1340_);
lean_ctor_set(v_reuseFailAlloc_1351_, 11, v_dynlibs_1341_);
lean_ctor_set(v_reuseFailAlloc_1351_, 12, v_plugins_1342_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*13, v_buildType_1328_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*13 + 1, v_backend_1339_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1343_);
lean_ctor_set_uint8(v_reuseFailAlloc_1351_, sizeof(void*)*13 + 3, v_allowNonModules_1344_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1363_){
_start:
{
lean_object* v_moreLeancArgs_1364_; 
v_moreLeancArgs_1364_ = lean_ctor_get(v_cfg_1363_, 3);
lean_inc_ref(v_moreLeancArgs_1364_);
return v_moreLeancArgs_1364_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1365_);
lean_dec_ref(v_cfg_1365_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1367_, lean_object* v_cfg_1368_){
_start:
{
uint8_t v_buildType_1369_; lean_object* v_leanOptions_1370_; lean_object* v_moreLeanArgs_1371_; lean_object* v_weakLeanArgs_1372_; lean_object* v_moreServerOptions_1373_; lean_object* v_weakLeancArgs_1374_; lean_object* v_moreLinkObjs_1375_; lean_object* v_moreLinkLibs_1376_; lean_object* v_moreLinkArgs_1377_; lean_object* v_weakLinkArgs_1378_; uint8_t v_backend_1379_; lean_object* v_platformIndependent_1380_; lean_object* v_dynlibs_1381_; lean_object* v_plugins_1382_; uint8_t v_requiresModuleSystem_1383_; uint8_t v_allowNonModules_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_buildType_1369_ = lean_ctor_get_uint8(v_cfg_1368_, sizeof(void*)*13);
v_leanOptions_1370_ = lean_ctor_get(v_cfg_1368_, 0);
v_moreLeanArgs_1371_ = lean_ctor_get(v_cfg_1368_, 1);
v_weakLeanArgs_1372_ = lean_ctor_get(v_cfg_1368_, 2);
v_moreServerOptions_1373_ = lean_ctor_get(v_cfg_1368_, 4);
v_weakLeancArgs_1374_ = lean_ctor_get(v_cfg_1368_, 5);
v_moreLinkObjs_1375_ = lean_ctor_get(v_cfg_1368_, 6);
v_moreLinkLibs_1376_ = lean_ctor_get(v_cfg_1368_, 7);
v_moreLinkArgs_1377_ = lean_ctor_get(v_cfg_1368_, 8);
v_weakLinkArgs_1378_ = lean_ctor_get(v_cfg_1368_, 9);
v_backend_1379_ = lean_ctor_get_uint8(v_cfg_1368_, sizeof(void*)*13 + 1);
v_platformIndependent_1380_ = lean_ctor_get(v_cfg_1368_, 10);
v_dynlibs_1381_ = lean_ctor_get(v_cfg_1368_, 11);
v_plugins_1382_ = lean_ctor_get(v_cfg_1368_, 12);
v_requiresModuleSystem_1383_ = lean_ctor_get_uint8(v_cfg_1368_, sizeof(void*)*13 + 2);
v_allowNonModules_1384_ = lean_ctor_get_uint8(v_cfg_1368_, sizeof(void*)*13 + 3);
v_isSharedCheck_1391_ = !lean_is_exclusive(v_cfg_1368_);
if (v_isSharedCheck_1391_ == 0)
{
lean_object* v_unused_1392_; 
v_unused_1392_ = lean_ctor_get(v_cfg_1368_, 3);
lean_dec(v_unused_1392_);
v___x_1386_ = v_cfg_1368_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_plugins_1382_);
lean_inc(v_dynlibs_1381_);
lean_inc(v_platformIndependent_1380_);
lean_inc(v_weakLinkArgs_1378_);
lean_inc(v_moreLinkArgs_1377_);
lean_inc(v_moreLinkLibs_1376_);
lean_inc(v_moreLinkObjs_1375_);
lean_inc(v_weakLeancArgs_1374_);
lean_inc(v_moreServerOptions_1373_);
lean_inc(v_weakLeanArgs_1372_);
lean_inc(v_moreLeanArgs_1371_);
lean_inc(v_leanOptions_1370_);
lean_dec(v_cfg_1368_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 3, v_val_1367_);
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_leanOptions_1370_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_moreLeanArgs_1371_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_weakLeanArgs_1372_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_val_1367_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_moreServerOptions_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v_weakLeancArgs_1374_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v_moreLinkObjs_1375_);
lean_ctor_set(v_reuseFailAlloc_1390_, 7, v_moreLinkLibs_1376_);
lean_ctor_set(v_reuseFailAlloc_1390_, 8, v_moreLinkArgs_1377_);
lean_ctor_set(v_reuseFailAlloc_1390_, 9, v_weakLinkArgs_1378_);
lean_ctor_set(v_reuseFailAlloc_1390_, 10, v_platformIndependent_1380_);
lean_ctor_set(v_reuseFailAlloc_1390_, 11, v_dynlibs_1381_);
lean_ctor_set(v_reuseFailAlloc_1390_, 12, v_plugins_1382_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*13, v_buildType_1369_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*13 + 1, v_backend_1379_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1390_, sizeof(void*)*13 + 3, v_allowNonModules_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1393_, lean_object* v_cfg_1394_){
_start:
{
uint8_t v_buildType_1395_; lean_object* v_leanOptions_1396_; lean_object* v_moreLeanArgs_1397_; lean_object* v_weakLeanArgs_1398_; lean_object* v_moreLeancArgs_1399_; lean_object* v_moreServerOptions_1400_; lean_object* v_weakLeancArgs_1401_; lean_object* v_moreLinkObjs_1402_; lean_object* v_moreLinkLibs_1403_; lean_object* v_moreLinkArgs_1404_; lean_object* v_weakLinkArgs_1405_; uint8_t v_backend_1406_; lean_object* v_platformIndependent_1407_; lean_object* v_dynlibs_1408_; lean_object* v_plugins_1409_; uint8_t v_requiresModuleSystem_1410_; uint8_t v_allowNonModules_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1419_; 
v_buildType_1395_ = lean_ctor_get_uint8(v_cfg_1394_, sizeof(void*)*13);
v_leanOptions_1396_ = lean_ctor_get(v_cfg_1394_, 0);
v_moreLeanArgs_1397_ = lean_ctor_get(v_cfg_1394_, 1);
v_weakLeanArgs_1398_ = lean_ctor_get(v_cfg_1394_, 2);
v_moreLeancArgs_1399_ = lean_ctor_get(v_cfg_1394_, 3);
v_moreServerOptions_1400_ = lean_ctor_get(v_cfg_1394_, 4);
v_weakLeancArgs_1401_ = lean_ctor_get(v_cfg_1394_, 5);
v_moreLinkObjs_1402_ = lean_ctor_get(v_cfg_1394_, 6);
v_moreLinkLibs_1403_ = lean_ctor_get(v_cfg_1394_, 7);
v_moreLinkArgs_1404_ = lean_ctor_get(v_cfg_1394_, 8);
v_weakLinkArgs_1405_ = lean_ctor_get(v_cfg_1394_, 9);
v_backend_1406_ = lean_ctor_get_uint8(v_cfg_1394_, sizeof(void*)*13 + 1);
v_platformIndependent_1407_ = lean_ctor_get(v_cfg_1394_, 10);
v_dynlibs_1408_ = lean_ctor_get(v_cfg_1394_, 11);
v_plugins_1409_ = lean_ctor_get(v_cfg_1394_, 12);
v_requiresModuleSystem_1410_ = lean_ctor_get_uint8(v_cfg_1394_, sizeof(void*)*13 + 2);
v_allowNonModules_1411_ = lean_ctor_get_uint8(v_cfg_1394_, sizeof(void*)*13 + 3);
v_isSharedCheck_1419_ = !lean_is_exclusive(v_cfg_1394_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1413_ = v_cfg_1394_;
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_plugins_1409_);
lean_inc(v_dynlibs_1408_);
lean_inc(v_platformIndependent_1407_);
lean_inc(v_weakLinkArgs_1405_);
lean_inc(v_moreLinkArgs_1404_);
lean_inc(v_moreLinkLibs_1403_);
lean_inc(v_moreLinkObjs_1402_);
lean_inc(v_weakLeancArgs_1401_);
lean_inc(v_moreServerOptions_1400_);
lean_inc(v_moreLeancArgs_1399_);
lean_inc(v_weakLeanArgs_1398_);
lean_inc(v_moreLeanArgs_1397_);
lean_inc(v_leanOptions_1396_);
lean_dec(v_cfg_1394_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1419_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
v___x_1415_ = lean_apply_1(v_f_1393_, v_moreLeancArgs_1399_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 3, v___x_1415_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_leanOptions_1396_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_moreLeanArgs_1397_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_weakLeanArgs_1398_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v___x_1415_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_moreServerOptions_1400_);
lean_ctor_set(v_reuseFailAlloc_1418_, 5, v_weakLeancArgs_1401_);
lean_ctor_set(v_reuseFailAlloc_1418_, 6, v_moreLinkObjs_1402_);
lean_ctor_set(v_reuseFailAlloc_1418_, 7, v_moreLinkLibs_1403_);
lean_ctor_set(v_reuseFailAlloc_1418_, 8, v_moreLinkArgs_1404_);
lean_ctor_set(v_reuseFailAlloc_1418_, 9, v_weakLinkArgs_1405_);
lean_ctor_set(v_reuseFailAlloc_1418_, 10, v_platformIndependent_1407_);
lean_ctor_set(v_reuseFailAlloc_1418_, 11, v_dynlibs_1408_);
lean_ctor_set(v_reuseFailAlloc_1418_, 12, v_plugins_1409_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13, v_buildType_1395_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 1, v_backend_1406_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1410_);
lean_ctor_set_uint8(v_reuseFailAlloc_1418_, sizeof(void*)*13 + 3, v_allowNonModules_1411_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1430_){
_start:
{
lean_object* v_moreServerOptions_1431_; 
v_moreServerOptions_1431_ = lean_ctor_get(v_cfg_1430_, 4);
lean_inc_ref(v_moreServerOptions_1431_);
return v_moreServerOptions_1431_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1432_);
lean_dec_ref(v_cfg_1432_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1434_, lean_object* v_cfg_1435_){
_start:
{
uint8_t v_buildType_1436_; lean_object* v_leanOptions_1437_; lean_object* v_moreLeanArgs_1438_; lean_object* v_weakLeanArgs_1439_; lean_object* v_moreLeancArgs_1440_; lean_object* v_weakLeancArgs_1441_; lean_object* v_moreLinkObjs_1442_; lean_object* v_moreLinkLibs_1443_; lean_object* v_moreLinkArgs_1444_; lean_object* v_weakLinkArgs_1445_; uint8_t v_backend_1446_; lean_object* v_platformIndependent_1447_; lean_object* v_dynlibs_1448_; lean_object* v_plugins_1449_; uint8_t v_requiresModuleSystem_1450_; uint8_t v_allowNonModules_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
v_buildType_1436_ = lean_ctor_get_uint8(v_cfg_1435_, sizeof(void*)*13);
v_leanOptions_1437_ = lean_ctor_get(v_cfg_1435_, 0);
v_moreLeanArgs_1438_ = lean_ctor_get(v_cfg_1435_, 1);
v_weakLeanArgs_1439_ = lean_ctor_get(v_cfg_1435_, 2);
v_moreLeancArgs_1440_ = lean_ctor_get(v_cfg_1435_, 3);
v_weakLeancArgs_1441_ = lean_ctor_get(v_cfg_1435_, 5);
v_moreLinkObjs_1442_ = lean_ctor_get(v_cfg_1435_, 6);
v_moreLinkLibs_1443_ = lean_ctor_get(v_cfg_1435_, 7);
v_moreLinkArgs_1444_ = lean_ctor_get(v_cfg_1435_, 8);
v_weakLinkArgs_1445_ = lean_ctor_get(v_cfg_1435_, 9);
v_backend_1446_ = lean_ctor_get_uint8(v_cfg_1435_, sizeof(void*)*13 + 1);
v_platformIndependent_1447_ = lean_ctor_get(v_cfg_1435_, 10);
v_dynlibs_1448_ = lean_ctor_get(v_cfg_1435_, 11);
v_plugins_1449_ = lean_ctor_get(v_cfg_1435_, 12);
v_requiresModuleSystem_1450_ = lean_ctor_get_uint8(v_cfg_1435_, sizeof(void*)*13 + 2);
v_allowNonModules_1451_ = lean_ctor_get_uint8(v_cfg_1435_, sizeof(void*)*13 + 3);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_cfg_1435_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v_cfg_1435_, 4);
lean_dec(v_unused_1459_);
v___x_1453_ = v_cfg_1435_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_plugins_1449_);
lean_inc(v_dynlibs_1448_);
lean_inc(v_platformIndependent_1447_);
lean_inc(v_weakLinkArgs_1445_);
lean_inc(v_moreLinkArgs_1444_);
lean_inc(v_moreLinkLibs_1443_);
lean_inc(v_moreLinkObjs_1442_);
lean_inc(v_weakLeancArgs_1441_);
lean_inc(v_moreLeancArgs_1440_);
lean_inc(v_weakLeanArgs_1439_);
lean_inc(v_moreLeanArgs_1438_);
lean_inc(v_leanOptions_1437_);
lean_dec(v_cfg_1435_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 4, v_val_1434_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_leanOptions_1437_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v_moreLeanArgs_1438_);
lean_ctor_set(v_reuseFailAlloc_1457_, 2, v_weakLeanArgs_1439_);
lean_ctor_set(v_reuseFailAlloc_1457_, 3, v_moreLeancArgs_1440_);
lean_ctor_set(v_reuseFailAlloc_1457_, 4, v_val_1434_);
lean_ctor_set(v_reuseFailAlloc_1457_, 5, v_weakLeancArgs_1441_);
lean_ctor_set(v_reuseFailAlloc_1457_, 6, v_moreLinkObjs_1442_);
lean_ctor_set(v_reuseFailAlloc_1457_, 7, v_moreLinkLibs_1443_);
lean_ctor_set(v_reuseFailAlloc_1457_, 8, v_moreLinkArgs_1444_);
lean_ctor_set(v_reuseFailAlloc_1457_, 9, v_weakLinkArgs_1445_);
lean_ctor_set(v_reuseFailAlloc_1457_, 10, v_platformIndependent_1447_);
lean_ctor_set(v_reuseFailAlloc_1457_, 11, v_dynlibs_1448_);
lean_ctor_set(v_reuseFailAlloc_1457_, 12, v_plugins_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*13, v_buildType_1436_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*13 + 1, v_backend_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1450_);
lean_ctor_set_uint8(v_reuseFailAlloc_1457_, sizeof(void*)*13 + 3, v_allowNonModules_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1460_, lean_object* v_cfg_1461_){
_start:
{
uint8_t v_buildType_1462_; lean_object* v_leanOptions_1463_; lean_object* v_moreLeanArgs_1464_; lean_object* v_weakLeanArgs_1465_; lean_object* v_moreLeancArgs_1466_; lean_object* v_moreServerOptions_1467_; lean_object* v_weakLeancArgs_1468_; lean_object* v_moreLinkObjs_1469_; lean_object* v_moreLinkLibs_1470_; lean_object* v_moreLinkArgs_1471_; lean_object* v_weakLinkArgs_1472_; uint8_t v_backend_1473_; lean_object* v_platformIndependent_1474_; lean_object* v_dynlibs_1475_; lean_object* v_plugins_1476_; uint8_t v_requiresModuleSystem_1477_; uint8_t v_allowNonModules_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1486_; 
v_buildType_1462_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*13);
v_leanOptions_1463_ = lean_ctor_get(v_cfg_1461_, 0);
v_moreLeanArgs_1464_ = lean_ctor_get(v_cfg_1461_, 1);
v_weakLeanArgs_1465_ = lean_ctor_get(v_cfg_1461_, 2);
v_moreLeancArgs_1466_ = lean_ctor_get(v_cfg_1461_, 3);
v_moreServerOptions_1467_ = lean_ctor_get(v_cfg_1461_, 4);
v_weakLeancArgs_1468_ = lean_ctor_get(v_cfg_1461_, 5);
v_moreLinkObjs_1469_ = lean_ctor_get(v_cfg_1461_, 6);
v_moreLinkLibs_1470_ = lean_ctor_get(v_cfg_1461_, 7);
v_moreLinkArgs_1471_ = lean_ctor_get(v_cfg_1461_, 8);
v_weakLinkArgs_1472_ = lean_ctor_get(v_cfg_1461_, 9);
v_backend_1473_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*13 + 1);
v_platformIndependent_1474_ = lean_ctor_get(v_cfg_1461_, 10);
v_dynlibs_1475_ = lean_ctor_get(v_cfg_1461_, 11);
v_plugins_1476_ = lean_ctor_get(v_cfg_1461_, 12);
v_requiresModuleSystem_1477_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*13 + 2);
v_allowNonModules_1478_ = lean_ctor_get_uint8(v_cfg_1461_, sizeof(void*)*13 + 3);
v_isSharedCheck_1486_ = !lean_is_exclusive(v_cfg_1461_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1480_ = v_cfg_1461_;
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_plugins_1476_);
lean_inc(v_dynlibs_1475_);
lean_inc(v_platformIndependent_1474_);
lean_inc(v_weakLinkArgs_1472_);
lean_inc(v_moreLinkArgs_1471_);
lean_inc(v_moreLinkLibs_1470_);
lean_inc(v_moreLinkObjs_1469_);
lean_inc(v_weakLeancArgs_1468_);
lean_inc(v_moreServerOptions_1467_);
lean_inc(v_moreLeancArgs_1466_);
lean_inc(v_weakLeanArgs_1465_);
lean_inc(v_moreLeanArgs_1464_);
lean_inc(v_leanOptions_1463_);
lean_dec(v_cfg_1461_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1486_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1484_; 
v___x_1482_ = lean_apply_1(v_f_1460_, v_moreServerOptions_1467_);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 4, v___x_1482_);
v___x_1484_ = v___x_1480_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_leanOptions_1463_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v_moreLeanArgs_1464_);
lean_ctor_set(v_reuseFailAlloc_1485_, 2, v_weakLeanArgs_1465_);
lean_ctor_set(v_reuseFailAlloc_1485_, 3, v_moreLeancArgs_1466_);
lean_ctor_set(v_reuseFailAlloc_1485_, 4, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1485_, 5, v_weakLeancArgs_1468_);
lean_ctor_set(v_reuseFailAlloc_1485_, 6, v_moreLinkObjs_1469_);
lean_ctor_set(v_reuseFailAlloc_1485_, 7, v_moreLinkLibs_1470_);
lean_ctor_set(v_reuseFailAlloc_1485_, 8, v_moreLinkArgs_1471_);
lean_ctor_set(v_reuseFailAlloc_1485_, 9, v_weakLinkArgs_1472_);
lean_ctor_set(v_reuseFailAlloc_1485_, 10, v_platformIndependent_1474_);
lean_ctor_set(v_reuseFailAlloc_1485_, 11, v_dynlibs_1475_);
lean_ctor_set(v_reuseFailAlloc_1485_, 12, v_plugins_1476_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*13, v_buildType_1462_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*13 + 1, v_backend_1473_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1477_);
lean_ctor_set_uint8(v_reuseFailAlloc_1485_, sizeof(void*)*13 + 3, v_allowNonModules_1478_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1497_){
_start:
{
lean_object* v_weakLeancArgs_1498_; 
v_weakLeancArgs_1498_ = lean_ctor_get(v_cfg_1497_, 5);
lean_inc_ref(v_weakLeancArgs_1498_);
return v_weakLeancArgs_1498_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1499_);
lean_dec_ref(v_cfg_1499_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1501_, lean_object* v_cfg_1502_){
_start:
{
uint8_t v_buildType_1503_; lean_object* v_leanOptions_1504_; lean_object* v_moreLeanArgs_1505_; lean_object* v_weakLeanArgs_1506_; lean_object* v_moreLeancArgs_1507_; lean_object* v_moreServerOptions_1508_; lean_object* v_moreLinkObjs_1509_; lean_object* v_moreLinkLibs_1510_; lean_object* v_moreLinkArgs_1511_; lean_object* v_weakLinkArgs_1512_; uint8_t v_backend_1513_; lean_object* v_platformIndependent_1514_; lean_object* v_dynlibs_1515_; lean_object* v_plugins_1516_; uint8_t v_requiresModuleSystem_1517_; uint8_t v_allowNonModules_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_buildType_1503_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*13);
v_leanOptions_1504_ = lean_ctor_get(v_cfg_1502_, 0);
v_moreLeanArgs_1505_ = lean_ctor_get(v_cfg_1502_, 1);
v_weakLeanArgs_1506_ = lean_ctor_get(v_cfg_1502_, 2);
v_moreLeancArgs_1507_ = lean_ctor_get(v_cfg_1502_, 3);
v_moreServerOptions_1508_ = lean_ctor_get(v_cfg_1502_, 4);
v_moreLinkObjs_1509_ = lean_ctor_get(v_cfg_1502_, 6);
v_moreLinkLibs_1510_ = lean_ctor_get(v_cfg_1502_, 7);
v_moreLinkArgs_1511_ = lean_ctor_get(v_cfg_1502_, 8);
v_weakLinkArgs_1512_ = lean_ctor_get(v_cfg_1502_, 9);
v_backend_1513_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*13 + 1);
v_platformIndependent_1514_ = lean_ctor_get(v_cfg_1502_, 10);
v_dynlibs_1515_ = lean_ctor_get(v_cfg_1502_, 11);
v_plugins_1516_ = lean_ctor_get(v_cfg_1502_, 12);
v_requiresModuleSystem_1517_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*13 + 2);
v_allowNonModules_1518_ = lean_ctor_get_uint8(v_cfg_1502_, sizeof(void*)*13 + 3);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_cfg_1502_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v_cfg_1502_, 5);
lean_dec(v_unused_1526_);
v___x_1520_ = v_cfg_1502_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_plugins_1516_);
lean_inc(v_dynlibs_1515_);
lean_inc(v_platformIndependent_1514_);
lean_inc(v_weakLinkArgs_1512_);
lean_inc(v_moreLinkArgs_1511_);
lean_inc(v_moreLinkLibs_1510_);
lean_inc(v_moreLinkObjs_1509_);
lean_inc(v_moreServerOptions_1508_);
lean_inc(v_moreLeancArgs_1507_);
lean_inc(v_weakLeanArgs_1506_);
lean_inc(v_moreLeanArgs_1505_);
lean_inc(v_leanOptions_1504_);
lean_dec(v_cfg_1502_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 5, v_val_1501_);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_leanOptions_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_moreLeanArgs_1505_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_weakLeanArgs_1506_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_moreLeancArgs_1507_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_moreServerOptions_1508_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v_val_1501_);
lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_moreLinkObjs_1509_);
lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_moreLinkLibs_1510_);
lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_moreLinkArgs_1511_);
lean_ctor_set(v_reuseFailAlloc_1524_, 9, v_weakLinkArgs_1512_);
lean_ctor_set(v_reuseFailAlloc_1524_, 10, v_platformIndependent_1514_);
lean_ctor_set(v_reuseFailAlloc_1524_, 11, v_dynlibs_1515_);
lean_ctor_set(v_reuseFailAlloc_1524_, 12, v_plugins_1516_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13, v_buildType_1503_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 1, v_backend_1513_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1517_);
lean_ctor_set_uint8(v_reuseFailAlloc_1524_, sizeof(void*)*13 + 3, v_allowNonModules_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1527_, lean_object* v_cfg_1528_){
_start:
{
uint8_t v_buildType_1529_; lean_object* v_leanOptions_1530_; lean_object* v_moreLeanArgs_1531_; lean_object* v_weakLeanArgs_1532_; lean_object* v_moreLeancArgs_1533_; lean_object* v_moreServerOptions_1534_; lean_object* v_weakLeancArgs_1535_; lean_object* v_moreLinkObjs_1536_; lean_object* v_moreLinkLibs_1537_; lean_object* v_moreLinkArgs_1538_; lean_object* v_weakLinkArgs_1539_; uint8_t v_backend_1540_; lean_object* v_platformIndependent_1541_; lean_object* v_dynlibs_1542_; lean_object* v_plugins_1543_; uint8_t v_requiresModuleSystem_1544_; uint8_t v_allowNonModules_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
v_buildType_1529_ = lean_ctor_get_uint8(v_cfg_1528_, sizeof(void*)*13);
v_leanOptions_1530_ = lean_ctor_get(v_cfg_1528_, 0);
v_moreLeanArgs_1531_ = lean_ctor_get(v_cfg_1528_, 1);
v_weakLeanArgs_1532_ = lean_ctor_get(v_cfg_1528_, 2);
v_moreLeancArgs_1533_ = lean_ctor_get(v_cfg_1528_, 3);
v_moreServerOptions_1534_ = lean_ctor_get(v_cfg_1528_, 4);
v_weakLeancArgs_1535_ = lean_ctor_get(v_cfg_1528_, 5);
v_moreLinkObjs_1536_ = lean_ctor_get(v_cfg_1528_, 6);
v_moreLinkLibs_1537_ = lean_ctor_get(v_cfg_1528_, 7);
v_moreLinkArgs_1538_ = lean_ctor_get(v_cfg_1528_, 8);
v_weakLinkArgs_1539_ = lean_ctor_get(v_cfg_1528_, 9);
v_backend_1540_ = lean_ctor_get_uint8(v_cfg_1528_, sizeof(void*)*13 + 1);
v_platformIndependent_1541_ = lean_ctor_get(v_cfg_1528_, 10);
v_dynlibs_1542_ = lean_ctor_get(v_cfg_1528_, 11);
v_plugins_1543_ = lean_ctor_get(v_cfg_1528_, 12);
v_requiresModuleSystem_1544_ = lean_ctor_get_uint8(v_cfg_1528_, sizeof(void*)*13 + 2);
v_allowNonModules_1545_ = lean_ctor_get_uint8(v_cfg_1528_, sizeof(void*)*13 + 3);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_cfg_1528_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1547_ = v_cfg_1528_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_plugins_1543_);
lean_inc(v_dynlibs_1542_);
lean_inc(v_platformIndependent_1541_);
lean_inc(v_weakLinkArgs_1539_);
lean_inc(v_moreLinkArgs_1538_);
lean_inc(v_moreLinkLibs_1537_);
lean_inc(v_moreLinkObjs_1536_);
lean_inc(v_weakLeancArgs_1535_);
lean_inc(v_moreServerOptions_1534_);
lean_inc(v_moreLeancArgs_1533_);
lean_inc(v_weakLeanArgs_1532_);
lean_inc(v_moreLeanArgs_1531_);
lean_inc(v_leanOptions_1530_);
lean_dec(v_cfg_1528_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = lean_apply_1(v_f_1527_, v_weakLeancArgs_1535_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 5, v___x_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_leanOptions_1530_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_moreLeanArgs_1531_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_weakLeanArgs_1532_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_moreLeancArgs_1533_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_moreServerOptions_1534_);
lean_ctor_set(v_reuseFailAlloc_1552_, 5, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1552_, 6, v_moreLinkObjs_1536_);
lean_ctor_set(v_reuseFailAlloc_1552_, 7, v_moreLinkLibs_1537_);
lean_ctor_set(v_reuseFailAlloc_1552_, 8, v_moreLinkArgs_1538_);
lean_ctor_set(v_reuseFailAlloc_1552_, 9, v_weakLinkArgs_1539_);
lean_ctor_set(v_reuseFailAlloc_1552_, 10, v_platformIndependent_1541_);
lean_ctor_set(v_reuseFailAlloc_1552_, 11, v_dynlibs_1542_);
lean_ctor_set(v_reuseFailAlloc_1552_, 12, v_plugins_1543_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*13, v_buildType_1529_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*13 + 1, v_backend_1540_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1544_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*13 + 3, v_allowNonModules_1545_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1564_){
_start:
{
lean_object* v_moreLinkObjs_1565_; 
v_moreLinkObjs_1565_ = lean_ctor_get(v_cfg_1564_, 6);
lean_inc_ref(v_moreLinkObjs_1565_);
return v_moreLinkObjs_1565_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1566_);
lean_dec_ref(v_cfg_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1568_, lean_object* v_cfg_1569_){
_start:
{
uint8_t v_buildType_1570_; lean_object* v_leanOptions_1571_; lean_object* v_moreLeanArgs_1572_; lean_object* v_weakLeanArgs_1573_; lean_object* v_moreLeancArgs_1574_; lean_object* v_moreServerOptions_1575_; lean_object* v_weakLeancArgs_1576_; lean_object* v_moreLinkLibs_1577_; lean_object* v_moreLinkArgs_1578_; lean_object* v_weakLinkArgs_1579_; uint8_t v_backend_1580_; lean_object* v_platformIndependent_1581_; lean_object* v_dynlibs_1582_; lean_object* v_plugins_1583_; uint8_t v_requiresModuleSystem_1584_; uint8_t v_allowNonModules_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_buildType_1570_ = lean_ctor_get_uint8(v_cfg_1569_, sizeof(void*)*13);
v_leanOptions_1571_ = lean_ctor_get(v_cfg_1569_, 0);
v_moreLeanArgs_1572_ = lean_ctor_get(v_cfg_1569_, 1);
v_weakLeanArgs_1573_ = lean_ctor_get(v_cfg_1569_, 2);
v_moreLeancArgs_1574_ = lean_ctor_get(v_cfg_1569_, 3);
v_moreServerOptions_1575_ = lean_ctor_get(v_cfg_1569_, 4);
v_weakLeancArgs_1576_ = lean_ctor_get(v_cfg_1569_, 5);
v_moreLinkLibs_1577_ = lean_ctor_get(v_cfg_1569_, 7);
v_moreLinkArgs_1578_ = lean_ctor_get(v_cfg_1569_, 8);
v_weakLinkArgs_1579_ = lean_ctor_get(v_cfg_1569_, 9);
v_backend_1580_ = lean_ctor_get_uint8(v_cfg_1569_, sizeof(void*)*13 + 1);
v_platformIndependent_1581_ = lean_ctor_get(v_cfg_1569_, 10);
v_dynlibs_1582_ = lean_ctor_get(v_cfg_1569_, 11);
v_plugins_1583_ = lean_ctor_get(v_cfg_1569_, 12);
v_requiresModuleSystem_1584_ = lean_ctor_get_uint8(v_cfg_1569_, sizeof(void*)*13 + 2);
v_allowNonModules_1585_ = lean_ctor_get_uint8(v_cfg_1569_, sizeof(void*)*13 + 3);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_cfg_1569_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_cfg_1569_, 6);
lean_dec(v_unused_1593_);
v___x_1587_ = v_cfg_1569_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_plugins_1583_);
lean_inc(v_dynlibs_1582_);
lean_inc(v_platformIndependent_1581_);
lean_inc(v_weakLinkArgs_1579_);
lean_inc(v_moreLinkArgs_1578_);
lean_inc(v_moreLinkLibs_1577_);
lean_inc(v_weakLeancArgs_1576_);
lean_inc(v_moreServerOptions_1575_);
lean_inc(v_moreLeancArgs_1574_);
lean_inc(v_weakLeanArgs_1573_);
lean_inc(v_moreLeanArgs_1572_);
lean_inc(v_leanOptions_1571_);
lean_dec(v_cfg_1569_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 6, v_val_1568_);
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_leanOptions_1571_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_moreLeanArgs_1572_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_weakLeanArgs_1573_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_moreLeancArgs_1574_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_moreServerOptions_1575_);
lean_ctor_set(v_reuseFailAlloc_1591_, 5, v_weakLeancArgs_1576_);
lean_ctor_set(v_reuseFailAlloc_1591_, 6, v_val_1568_);
lean_ctor_set(v_reuseFailAlloc_1591_, 7, v_moreLinkLibs_1577_);
lean_ctor_set(v_reuseFailAlloc_1591_, 8, v_moreLinkArgs_1578_);
lean_ctor_set(v_reuseFailAlloc_1591_, 9, v_weakLinkArgs_1579_);
lean_ctor_set(v_reuseFailAlloc_1591_, 10, v_platformIndependent_1581_);
lean_ctor_set(v_reuseFailAlloc_1591_, 11, v_dynlibs_1582_);
lean_ctor_set(v_reuseFailAlloc_1591_, 12, v_plugins_1583_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13, v_buildType_1570_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 1, v_backend_1580_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1584_);
lean_ctor_set_uint8(v_reuseFailAlloc_1591_, sizeof(void*)*13 + 3, v_allowNonModules_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1594_, lean_object* v_cfg_1595_){
_start:
{
uint8_t v_buildType_1596_; lean_object* v_leanOptions_1597_; lean_object* v_moreLeanArgs_1598_; lean_object* v_weakLeanArgs_1599_; lean_object* v_moreLeancArgs_1600_; lean_object* v_moreServerOptions_1601_; lean_object* v_weakLeancArgs_1602_; lean_object* v_moreLinkObjs_1603_; lean_object* v_moreLinkLibs_1604_; lean_object* v_moreLinkArgs_1605_; lean_object* v_weakLinkArgs_1606_; uint8_t v_backend_1607_; lean_object* v_platformIndependent_1608_; lean_object* v_dynlibs_1609_; lean_object* v_plugins_1610_; uint8_t v_requiresModuleSystem_1611_; uint8_t v_allowNonModules_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_buildType_1596_ = lean_ctor_get_uint8(v_cfg_1595_, sizeof(void*)*13);
v_leanOptions_1597_ = lean_ctor_get(v_cfg_1595_, 0);
v_moreLeanArgs_1598_ = lean_ctor_get(v_cfg_1595_, 1);
v_weakLeanArgs_1599_ = lean_ctor_get(v_cfg_1595_, 2);
v_moreLeancArgs_1600_ = lean_ctor_get(v_cfg_1595_, 3);
v_moreServerOptions_1601_ = lean_ctor_get(v_cfg_1595_, 4);
v_weakLeancArgs_1602_ = lean_ctor_get(v_cfg_1595_, 5);
v_moreLinkObjs_1603_ = lean_ctor_get(v_cfg_1595_, 6);
v_moreLinkLibs_1604_ = lean_ctor_get(v_cfg_1595_, 7);
v_moreLinkArgs_1605_ = lean_ctor_get(v_cfg_1595_, 8);
v_weakLinkArgs_1606_ = lean_ctor_get(v_cfg_1595_, 9);
v_backend_1607_ = lean_ctor_get_uint8(v_cfg_1595_, sizeof(void*)*13 + 1);
v_platformIndependent_1608_ = lean_ctor_get(v_cfg_1595_, 10);
v_dynlibs_1609_ = lean_ctor_get(v_cfg_1595_, 11);
v_plugins_1610_ = lean_ctor_get(v_cfg_1595_, 12);
v_requiresModuleSystem_1611_ = lean_ctor_get_uint8(v_cfg_1595_, sizeof(void*)*13 + 2);
v_allowNonModules_1612_ = lean_ctor_get_uint8(v_cfg_1595_, sizeof(void*)*13 + 3);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_cfg_1595_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v_cfg_1595_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_plugins_1610_);
lean_inc(v_dynlibs_1609_);
lean_inc(v_platformIndependent_1608_);
lean_inc(v_weakLinkArgs_1606_);
lean_inc(v_moreLinkArgs_1605_);
lean_inc(v_moreLinkLibs_1604_);
lean_inc(v_moreLinkObjs_1603_);
lean_inc(v_weakLeancArgs_1602_);
lean_inc(v_moreServerOptions_1601_);
lean_inc(v_moreLeancArgs_1600_);
lean_inc(v_weakLeanArgs_1599_);
lean_inc(v_moreLeanArgs_1598_);
lean_inc(v_leanOptions_1597_);
lean_dec(v_cfg_1595_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_apply_1(v_f_1594_, v_moreLinkObjs_1603_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 6, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_leanOptions_1597_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_moreLeanArgs_1598_);
lean_ctor_set(v_reuseFailAlloc_1619_, 2, v_weakLeanArgs_1599_);
lean_ctor_set(v_reuseFailAlloc_1619_, 3, v_moreLeancArgs_1600_);
lean_ctor_set(v_reuseFailAlloc_1619_, 4, v_moreServerOptions_1601_);
lean_ctor_set(v_reuseFailAlloc_1619_, 5, v_weakLeancArgs_1602_);
lean_ctor_set(v_reuseFailAlloc_1619_, 6, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1619_, 7, v_moreLinkLibs_1604_);
lean_ctor_set(v_reuseFailAlloc_1619_, 8, v_moreLinkArgs_1605_);
lean_ctor_set(v_reuseFailAlloc_1619_, 9, v_weakLinkArgs_1606_);
lean_ctor_set(v_reuseFailAlloc_1619_, 10, v_platformIndependent_1608_);
lean_ctor_set(v_reuseFailAlloc_1619_, 11, v_dynlibs_1609_);
lean_ctor_set(v_reuseFailAlloc_1619_, 12, v_plugins_1610_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*13, v_buildType_1596_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*13 + 1, v_backend_1607_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1611_);
lean_ctor_set_uint8(v_reuseFailAlloc_1619_, sizeof(void*)*13 + 3, v_allowNonModules_1612_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1625_);
lean_dec_ref(v_x_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1638_){
_start:
{
lean_object* v_moreLinkLibs_1639_; 
v_moreLinkLibs_1639_ = lean_ctor_get(v_cfg_1638_, 7);
lean_inc_ref(v_moreLinkLibs_1639_);
return v_moreLinkLibs_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1640_);
lean_dec_ref(v_cfg_1640_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1642_, lean_object* v_cfg_1643_){
_start:
{
uint8_t v_buildType_1644_; lean_object* v_leanOptions_1645_; lean_object* v_moreLeanArgs_1646_; lean_object* v_weakLeanArgs_1647_; lean_object* v_moreLeancArgs_1648_; lean_object* v_moreServerOptions_1649_; lean_object* v_weakLeancArgs_1650_; lean_object* v_moreLinkObjs_1651_; lean_object* v_moreLinkArgs_1652_; lean_object* v_weakLinkArgs_1653_; uint8_t v_backend_1654_; lean_object* v_platformIndependent_1655_; lean_object* v_dynlibs_1656_; lean_object* v_plugins_1657_; uint8_t v_requiresModuleSystem_1658_; uint8_t v_allowNonModules_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1666_; 
v_buildType_1644_ = lean_ctor_get_uint8(v_cfg_1643_, sizeof(void*)*13);
v_leanOptions_1645_ = lean_ctor_get(v_cfg_1643_, 0);
v_moreLeanArgs_1646_ = lean_ctor_get(v_cfg_1643_, 1);
v_weakLeanArgs_1647_ = lean_ctor_get(v_cfg_1643_, 2);
v_moreLeancArgs_1648_ = lean_ctor_get(v_cfg_1643_, 3);
v_moreServerOptions_1649_ = lean_ctor_get(v_cfg_1643_, 4);
v_weakLeancArgs_1650_ = lean_ctor_get(v_cfg_1643_, 5);
v_moreLinkObjs_1651_ = lean_ctor_get(v_cfg_1643_, 6);
v_moreLinkArgs_1652_ = lean_ctor_get(v_cfg_1643_, 8);
v_weakLinkArgs_1653_ = lean_ctor_get(v_cfg_1643_, 9);
v_backend_1654_ = lean_ctor_get_uint8(v_cfg_1643_, sizeof(void*)*13 + 1);
v_platformIndependent_1655_ = lean_ctor_get(v_cfg_1643_, 10);
v_dynlibs_1656_ = lean_ctor_get(v_cfg_1643_, 11);
v_plugins_1657_ = lean_ctor_get(v_cfg_1643_, 12);
v_requiresModuleSystem_1658_ = lean_ctor_get_uint8(v_cfg_1643_, sizeof(void*)*13 + 2);
v_allowNonModules_1659_ = lean_ctor_get_uint8(v_cfg_1643_, sizeof(void*)*13 + 3);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_cfg_1643_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; 
v_unused_1667_ = lean_ctor_get(v_cfg_1643_, 7);
lean_dec(v_unused_1667_);
v___x_1661_ = v_cfg_1643_;
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_plugins_1657_);
lean_inc(v_dynlibs_1656_);
lean_inc(v_platformIndependent_1655_);
lean_inc(v_weakLinkArgs_1653_);
lean_inc(v_moreLinkArgs_1652_);
lean_inc(v_moreLinkObjs_1651_);
lean_inc(v_weakLeancArgs_1650_);
lean_inc(v_moreServerOptions_1649_);
lean_inc(v_moreLeancArgs_1648_);
lean_inc(v_weakLeanArgs_1647_);
lean_inc(v_moreLeanArgs_1646_);
lean_inc(v_leanOptions_1645_);
lean_dec(v_cfg_1643_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1666_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 7, v_val_1642_);
v___x_1664_ = v___x_1661_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_leanOptions_1645_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_moreLeanArgs_1646_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v_weakLeanArgs_1647_);
lean_ctor_set(v_reuseFailAlloc_1665_, 3, v_moreLeancArgs_1648_);
lean_ctor_set(v_reuseFailAlloc_1665_, 4, v_moreServerOptions_1649_);
lean_ctor_set(v_reuseFailAlloc_1665_, 5, v_weakLeancArgs_1650_);
lean_ctor_set(v_reuseFailAlloc_1665_, 6, v_moreLinkObjs_1651_);
lean_ctor_set(v_reuseFailAlloc_1665_, 7, v_val_1642_);
lean_ctor_set(v_reuseFailAlloc_1665_, 8, v_moreLinkArgs_1652_);
lean_ctor_set(v_reuseFailAlloc_1665_, 9, v_weakLinkArgs_1653_);
lean_ctor_set(v_reuseFailAlloc_1665_, 10, v_platformIndependent_1655_);
lean_ctor_set(v_reuseFailAlloc_1665_, 11, v_dynlibs_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 12, v_plugins_1657_);
lean_ctor_set_uint8(v_reuseFailAlloc_1665_, sizeof(void*)*13, v_buildType_1644_);
lean_ctor_set_uint8(v_reuseFailAlloc_1665_, sizeof(void*)*13 + 1, v_backend_1654_);
lean_ctor_set_uint8(v_reuseFailAlloc_1665_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1658_);
lean_ctor_set_uint8(v_reuseFailAlloc_1665_, sizeof(void*)*13 + 3, v_allowNonModules_1659_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1668_, lean_object* v_cfg_1669_){
_start:
{
uint8_t v_buildType_1670_; lean_object* v_leanOptions_1671_; lean_object* v_moreLeanArgs_1672_; lean_object* v_weakLeanArgs_1673_; lean_object* v_moreLeancArgs_1674_; lean_object* v_moreServerOptions_1675_; lean_object* v_weakLeancArgs_1676_; lean_object* v_moreLinkObjs_1677_; lean_object* v_moreLinkLibs_1678_; lean_object* v_moreLinkArgs_1679_; lean_object* v_weakLinkArgs_1680_; uint8_t v_backend_1681_; lean_object* v_platformIndependent_1682_; lean_object* v_dynlibs_1683_; lean_object* v_plugins_1684_; uint8_t v_requiresModuleSystem_1685_; uint8_t v_allowNonModules_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
v_buildType_1670_ = lean_ctor_get_uint8(v_cfg_1669_, sizeof(void*)*13);
v_leanOptions_1671_ = lean_ctor_get(v_cfg_1669_, 0);
v_moreLeanArgs_1672_ = lean_ctor_get(v_cfg_1669_, 1);
v_weakLeanArgs_1673_ = lean_ctor_get(v_cfg_1669_, 2);
v_moreLeancArgs_1674_ = lean_ctor_get(v_cfg_1669_, 3);
v_moreServerOptions_1675_ = lean_ctor_get(v_cfg_1669_, 4);
v_weakLeancArgs_1676_ = lean_ctor_get(v_cfg_1669_, 5);
v_moreLinkObjs_1677_ = lean_ctor_get(v_cfg_1669_, 6);
v_moreLinkLibs_1678_ = lean_ctor_get(v_cfg_1669_, 7);
v_moreLinkArgs_1679_ = lean_ctor_get(v_cfg_1669_, 8);
v_weakLinkArgs_1680_ = lean_ctor_get(v_cfg_1669_, 9);
v_backend_1681_ = lean_ctor_get_uint8(v_cfg_1669_, sizeof(void*)*13 + 1);
v_platformIndependent_1682_ = lean_ctor_get(v_cfg_1669_, 10);
v_dynlibs_1683_ = lean_ctor_get(v_cfg_1669_, 11);
v_plugins_1684_ = lean_ctor_get(v_cfg_1669_, 12);
v_requiresModuleSystem_1685_ = lean_ctor_get_uint8(v_cfg_1669_, sizeof(void*)*13 + 2);
v_allowNonModules_1686_ = lean_ctor_get_uint8(v_cfg_1669_, sizeof(void*)*13 + 3);
v_isSharedCheck_1694_ = !lean_is_exclusive(v_cfg_1669_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1688_ = v_cfg_1669_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_plugins_1684_);
lean_inc(v_dynlibs_1683_);
lean_inc(v_platformIndependent_1682_);
lean_inc(v_weakLinkArgs_1680_);
lean_inc(v_moreLinkArgs_1679_);
lean_inc(v_moreLinkLibs_1678_);
lean_inc(v_moreLinkObjs_1677_);
lean_inc(v_weakLeancArgs_1676_);
lean_inc(v_moreServerOptions_1675_);
lean_inc(v_moreLeancArgs_1674_);
lean_inc(v_weakLeanArgs_1673_);
lean_inc(v_moreLeanArgs_1672_);
lean_inc(v_leanOptions_1671_);
lean_dec(v_cfg_1669_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_apply_1(v_f_1668_, v_moreLinkLibs_1678_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 7, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_leanOptions_1671_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_moreLeanArgs_1672_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_weakLeanArgs_1673_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_moreLeancArgs_1674_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_moreServerOptions_1675_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v_weakLeancArgs_1676_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_moreLinkObjs_1677_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_moreLinkArgs_1679_);
lean_ctor_set(v_reuseFailAlloc_1693_, 9, v_weakLinkArgs_1680_);
lean_ctor_set(v_reuseFailAlloc_1693_, 10, v_platformIndependent_1682_);
lean_ctor_set(v_reuseFailAlloc_1693_, 11, v_dynlibs_1683_);
lean_ctor_set(v_reuseFailAlloc_1693_, 12, v_plugins_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13, v_buildType_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13 + 1, v_backend_1681_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1693_, sizeof(void*)*13 + 3, v_allowNonModules_1686_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1705_){
_start:
{
lean_object* v_moreLinkArgs_1706_; 
v_moreLinkArgs_1706_ = lean_ctor_get(v_cfg_1705_, 8);
lean_inc_ref(v_moreLinkArgs_1706_);
return v_moreLinkArgs_1706_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1707_);
lean_dec_ref(v_cfg_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1709_, lean_object* v_cfg_1710_){
_start:
{
uint8_t v_buildType_1711_; lean_object* v_leanOptions_1712_; lean_object* v_moreLeanArgs_1713_; lean_object* v_weakLeanArgs_1714_; lean_object* v_moreLeancArgs_1715_; lean_object* v_moreServerOptions_1716_; lean_object* v_weakLeancArgs_1717_; lean_object* v_moreLinkObjs_1718_; lean_object* v_moreLinkLibs_1719_; lean_object* v_weakLinkArgs_1720_; uint8_t v_backend_1721_; lean_object* v_platformIndependent_1722_; lean_object* v_dynlibs_1723_; lean_object* v_plugins_1724_; uint8_t v_requiresModuleSystem_1725_; uint8_t v_allowNonModules_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_buildType_1711_ = lean_ctor_get_uint8(v_cfg_1710_, sizeof(void*)*13);
v_leanOptions_1712_ = lean_ctor_get(v_cfg_1710_, 0);
v_moreLeanArgs_1713_ = lean_ctor_get(v_cfg_1710_, 1);
v_weakLeanArgs_1714_ = lean_ctor_get(v_cfg_1710_, 2);
v_moreLeancArgs_1715_ = lean_ctor_get(v_cfg_1710_, 3);
v_moreServerOptions_1716_ = lean_ctor_get(v_cfg_1710_, 4);
v_weakLeancArgs_1717_ = lean_ctor_get(v_cfg_1710_, 5);
v_moreLinkObjs_1718_ = lean_ctor_get(v_cfg_1710_, 6);
v_moreLinkLibs_1719_ = lean_ctor_get(v_cfg_1710_, 7);
v_weakLinkArgs_1720_ = lean_ctor_get(v_cfg_1710_, 9);
v_backend_1721_ = lean_ctor_get_uint8(v_cfg_1710_, sizeof(void*)*13 + 1);
v_platformIndependent_1722_ = lean_ctor_get(v_cfg_1710_, 10);
v_dynlibs_1723_ = lean_ctor_get(v_cfg_1710_, 11);
v_plugins_1724_ = lean_ctor_get(v_cfg_1710_, 12);
v_requiresModuleSystem_1725_ = lean_ctor_get_uint8(v_cfg_1710_, sizeof(void*)*13 + 2);
v_allowNonModules_1726_ = lean_ctor_get_uint8(v_cfg_1710_, sizeof(void*)*13 + 3);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_cfg_1710_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v_cfg_1710_, 8);
lean_dec(v_unused_1734_);
v___x_1728_ = v_cfg_1710_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_plugins_1724_);
lean_inc(v_dynlibs_1723_);
lean_inc(v_platformIndependent_1722_);
lean_inc(v_weakLinkArgs_1720_);
lean_inc(v_moreLinkLibs_1719_);
lean_inc(v_moreLinkObjs_1718_);
lean_inc(v_weakLeancArgs_1717_);
lean_inc(v_moreServerOptions_1716_);
lean_inc(v_moreLeancArgs_1715_);
lean_inc(v_weakLeanArgs_1714_);
lean_inc(v_moreLeanArgs_1713_);
lean_inc(v_leanOptions_1712_);
lean_dec(v_cfg_1710_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 8, v_val_1709_);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_leanOptions_1712_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_moreLeanArgs_1713_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_weakLeanArgs_1714_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_moreLeancArgs_1715_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_moreServerOptions_1716_);
lean_ctor_set(v_reuseFailAlloc_1732_, 5, v_weakLeancArgs_1717_);
lean_ctor_set(v_reuseFailAlloc_1732_, 6, v_moreLinkObjs_1718_);
lean_ctor_set(v_reuseFailAlloc_1732_, 7, v_moreLinkLibs_1719_);
lean_ctor_set(v_reuseFailAlloc_1732_, 8, v_val_1709_);
lean_ctor_set(v_reuseFailAlloc_1732_, 9, v_weakLinkArgs_1720_);
lean_ctor_set(v_reuseFailAlloc_1732_, 10, v_platformIndependent_1722_);
lean_ctor_set(v_reuseFailAlloc_1732_, 11, v_dynlibs_1723_);
lean_ctor_set(v_reuseFailAlloc_1732_, 12, v_plugins_1724_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13, v_buildType_1711_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 1, v_backend_1721_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1725_);
lean_ctor_set_uint8(v_reuseFailAlloc_1732_, sizeof(void*)*13 + 3, v_allowNonModules_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1735_, lean_object* v_cfg_1736_){
_start:
{
uint8_t v_buildType_1737_; lean_object* v_leanOptions_1738_; lean_object* v_moreLeanArgs_1739_; lean_object* v_weakLeanArgs_1740_; lean_object* v_moreLeancArgs_1741_; lean_object* v_moreServerOptions_1742_; lean_object* v_weakLeancArgs_1743_; lean_object* v_moreLinkObjs_1744_; lean_object* v_moreLinkLibs_1745_; lean_object* v_moreLinkArgs_1746_; lean_object* v_weakLinkArgs_1747_; uint8_t v_backend_1748_; lean_object* v_platformIndependent_1749_; lean_object* v_dynlibs_1750_; lean_object* v_plugins_1751_; uint8_t v_requiresModuleSystem_1752_; uint8_t v_allowNonModules_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1761_; 
v_buildType_1737_ = lean_ctor_get_uint8(v_cfg_1736_, sizeof(void*)*13);
v_leanOptions_1738_ = lean_ctor_get(v_cfg_1736_, 0);
v_moreLeanArgs_1739_ = lean_ctor_get(v_cfg_1736_, 1);
v_weakLeanArgs_1740_ = lean_ctor_get(v_cfg_1736_, 2);
v_moreLeancArgs_1741_ = lean_ctor_get(v_cfg_1736_, 3);
v_moreServerOptions_1742_ = lean_ctor_get(v_cfg_1736_, 4);
v_weakLeancArgs_1743_ = lean_ctor_get(v_cfg_1736_, 5);
v_moreLinkObjs_1744_ = lean_ctor_get(v_cfg_1736_, 6);
v_moreLinkLibs_1745_ = lean_ctor_get(v_cfg_1736_, 7);
v_moreLinkArgs_1746_ = lean_ctor_get(v_cfg_1736_, 8);
v_weakLinkArgs_1747_ = lean_ctor_get(v_cfg_1736_, 9);
v_backend_1748_ = lean_ctor_get_uint8(v_cfg_1736_, sizeof(void*)*13 + 1);
v_platformIndependent_1749_ = lean_ctor_get(v_cfg_1736_, 10);
v_dynlibs_1750_ = lean_ctor_get(v_cfg_1736_, 11);
v_plugins_1751_ = lean_ctor_get(v_cfg_1736_, 12);
v_requiresModuleSystem_1752_ = lean_ctor_get_uint8(v_cfg_1736_, sizeof(void*)*13 + 2);
v_allowNonModules_1753_ = lean_ctor_get_uint8(v_cfg_1736_, sizeof(void*)*13 + 3);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_cfg_1736_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1755_ = v_cfg_1736_;
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_plugins_1751_);
lean_inc(v_dynlibs_1750_);
lean_inc(v_platformIndependent_1749_);
lean_inc(v_weakLinkArgs_1747_);
lean_inc(v_moreLinkArgs_1746_);
lean_inc(v_moreLinkLibs_1745_);
lean_inc(v_moreLinkObjs_1744_);
lean_inc(v_weakLeancArgs_1743_);
lean_inc(v_moreServerOptions_1742_);
lean_inc(v_moreLeancArgs_1741_);
lean_inc(v_weakLeanArgs_1740_);
lean_inc(v_moreLeanArgs_1739_);
lean_inc(v_leanOptions_1738_);
lean_dec(v_cfg_1736_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1761_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = lean_apply_1(v_f_1735_, v_moreLinkArgs_1746_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 8, v___x_1757_);
v___x_1759_ = v___x_1755_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_leanOptions_1738_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_moreLeanArgs_1739_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_weakLeanArgs_1740_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v_moreLeancArgs_1741_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v_moreServerOptions_1742_);
lean_ctor_set(v_reuseFailAlloc_1760_, 5, v_weakLeancArgs_1743_);
lean_ctor_set(v_reuseFailAlloc_1760_, 6, v_moreLinkObjs_1744_);
lean_ctor_set(v_reuseFailAlloc_1760_, 7, v_moreLinkLibs_1745_);
lean_ctor_set(v_reuseFailAlloc_1760_, 8, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1760_, 9, v_weakLinkArgs_1747_);
lean_ctor_set(v_reuseFailAlloc_1760_, 10, v_platformIndependent_1749_);
lean_ctor_set(v_reuseFailAlloc_1760_, 11, v_dynlibs_1750_);
lean_ctor_set(v_reuseFailAlloc_1760_, 12, v_plugins_1751_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13, v_buildType_1737_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13 + 1, v_backend_1748_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1752_);
lean_ctor_set_uint8(v_reuseFailAlloc_1760_, sizeof(void*)*13 + 3, v_allowNonModules_1753_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1772_){
_start:
{
lean_object* v_weakLinkArgs_1773_; 
v_weakLinkArgs_1773_ = lean_ctor_get(v_cfg_1772_, 9);
lean_inc_ref(v_weakLinkArgs_1773_);
return v_weakLinkArgs_1773_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1774_);
lean_dec_ref(v_cfg_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1776_, lean_object* v_cfg_1777_){
_start:
{
uint8_t v_buildType_1778_; lean_object* v_leanOptions_1779_; lean_object* v_moreLeanArgs_1780_; lean_object* v_weakLeanArgs_1781_; lean_object* v_moreLeancArgs_1782_; lean_object* v_moreServerOptions_1783_; lean_object* v_weakLeancArgs_1784_; lean_object* v_moreLinkObjs_1785_; lean_object* v_moreLinkLibs_1786_; lean_object* v_moreLinkArgs_1787_; uint8_t v_backend_1788_; lean_object* v_platformIndependent_1789_; lean_object* v_dynlibs_1790_; lean_object* v_plugins_1791_; uint8_t v_requiresModuleSystem_1792_; uint8_t v_allowNonModules_1793_; lean_object* v___x_1795_; uint8_t v_isShared_1796_; uint8_t v_isSharedCheck_1800_; 
v_buildType_1778_ = lean_ctor_get_uint8(v_cfg_1777_, sizeof(void*)*13);
v_leanOptions_1779_ = lean_ctor_get(v_cfg_1777_, 0);
v_moreLeanArgs_1780_ = lean_ctor_get(v_cfg_1777_, 1);
v_weakLeanArgs_1781_ = lean_ctor_get(v_cfg_1777_, 2);
v_moreLeancArgs_1782_ = lean_ctor_get(v_cfg_1777_, 3);
v_moreServerOptions_1783_ = lean_ctor_get(v_cfg_1777_, 4);
v_weakLeancArgs_1784_ = lean_ctor_get(v_cfg_1777_, 5);
v_moreLinkObjs_1785_ = lean_ctor_get(v_cfg_1777_, 6);
v_moreLinkLibs_1786_ = lean_ctor_get(v_cfg_1777_, 7);
v_moreLinkArgs_1787_ = lean_ctor_get(v_cfg_1777_, 8);
v_backend_1788_ = lean_ctor_get_uint8(v_cfg_1777_, sizeof(void*)*13 + 1);
v_platformIndependent_1789_ = lean_ctor_get(v_cfg_1777_, 10);
v_dynlibs_1790_ = lean_ctor_get(v_cfg_1777_, 11);
v_plugins_1791_ = lean_ctor_get(v_cfg_1777_, 12);
v_requiresModuleSystem_1792_ = lean_ctor_get_uint8(v_cfg_1777_, sizeof(void*)*13 + 2);
v_allowNonModules_1793_ = lean_ctor_get_uint8(v_cfg_1777_, sizeof(void*)*13 + 3);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_cfg_1777_);
if (v_isSharedCheck_1800_ == 0)
{
lean_object* v_unused_1801_; 
v_unused_1801_ = lean_ctor_get(v_cfg_1777_, 9);
lean_dec(v_unused_1801_);
v___x_1795_ = v_cfg_1777_;
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
else
{
lean_inc(v_plugins_1791_);
lean_inc(v_dynlibs_1790_);
lean_inc(v_platformIndependent_1789_);
lean_inc(v_moreLinkArgs_1787_);
lean_inc(v_moreLinkLibs_1786_);
lean_inc(v_moreLinkObjs_1785_);
lean_inc(v_weakLeancArgs_1784_);
lean_inc(v_moreServerOptions_1783_);
lean_inc(v_moreLeancArgs_1782_);
lean_inc(v_weakLeanArgs_1781_);
lean_inc(v_moreLeanArgs_1780_);
lean_inc(v_leanOptions_1779_);
lean_dec(v_cfg_1777_);
v___x_1795_ = lean_box(0);
v_isShared_1796_ = v_isSharedCheck_1800_;
goto v_resetjp_1794_;
}
v_resetjp_1794_:
{
lean_object* v___x_1798_; 
if (v_isShared_1796_ == 0)
{
lean_ctor_set(v___x_1795_, 9, v_val_1776_);
v___x_1798_ = v___x_1795_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1799_; 
v_reuseFailAlloc_1799_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1799_, 0, v_leanOptions_1779_);
lean_ctor_set(v_reuseFailAlloc_1799_, 1, v_moreLeanArgs_1780_);
lean_ctor_set(v_reuseFailAlloc_1799_, 2, v_weakLeanArgs_1781_);
lean_ctor_set(v_reuseFailAlloc_1799_, 3, v_moreLeancArgs_1782_);
lean_ctor_set(v_reuseFailAlloc_1799_, 4, v_moreServerOptions_1783_);
lean_ctor_set(v_reuseFailAlloc_1799_, 5, v_weakLeancArgs_1784_);
lean_ctor_set(v_reuseFailAlloc_1799_, 6, v_moreLinkObjs_1785_);
lean_ctor_set(v_reuseFailAlloc_1799_, 7, v_moreLinkLibs_1786_);
lean_ctor_set(v_reuseFailAlloc_1799_, 8, v_moreLinkArgs_1787_);
lean_ctor_set(v_reuseFailAlloc_1799_, 9, v_val_1776_);
lean_ctor_set(v_reuseFailAlloc_1799_, 10, v_platformIndependent_1789_);
lean_ctor_set(v_reuseFailAlloc_1799_, 11, v_dynlibs_1790_);
lean_ctor_set(v_reuseFailAlloc_1799_, 12, v_plugins_1791_);
lean_ctor_set_uint8(v_reuseFailAlloc_1799_, sizeof(void*)*13, v_buildType_1778_);
lean_ctor_set_uint8(v_reuseFailAlloc_1799_, sizeof(void*)*13 + 1, v_backend_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1799_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1799_, sizeof(void*)*13 + 3, v_allowNonModules_1793_);
v___x_1798_ = v_reuseFailAlloc_1799_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
return v___x_1798_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1802_, lean_object* v_cfg_1803_){
_start:
{
uint8_t v_buildType_1804_; lean_object* v_leanOptions_1805_; lean_object* v_moreLeanArgs_1806_; lean_object* v_weakLeanArgs_1807_; lean_object* v_moreLeancArgs_1808_; lean_object* v_moreServerOptions_1809_; lean_object* v_weakLeancArgs_1810_; lean_object* v_moreLinkObjs_1811_; lean_object* v_moreLinkLibs_1812_; lean_object* v_moreLinkArgs_1813_; lean_object* v_weakLinkArgs_1814_; uint8_t v_backend_1815_; lean_object* v_platformIndependent_1816_; lean_object* v_dynlibs_1817_; lean_object* v_plugins_1818_; uint8_t v_requiresModuleSystem_1819_; uint8_t v_allowNonModules_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1828_; 
v_buildType_1804_ = lean_ctor_get_uint8(v_cfg_1803_, sizeof(void*)*13);
v_leanOptions_1805_ = lean_ctor_get(v_cfg_1803_, 0);
v_moreLeanArgs_1806_ = lean_ctor_get(v_cfg_1803_, 1);
v_weakLeanArgs_1807_ = lean_ctor_get(v_cfg_1803_, 2);
v_moreLeancArgs_1808_ = lean_ctor_get(v_cfg_1803_, 3);
v_moreServerOptions_1809_ = lean_ctor_get(v_cfg_1803_, 4);
v_weakLeancArgs_1810_ = lean_ctor_get(v_cfg_1803_, 5);
v_moreLinkObjs_1811_ = lean_ctor_get(v_cfg_1803_, 6);
v_moreLinkLibs_1812_ = lean_ctor_get(v_cfg_1803_, 7);
v_moreLinkArgs_1813_ = lean_ctor_get(v_cfg_1803_, 8);
v_weakLinkArgs_1814_ = lean_ctor_get(v_cfg_1803_, 9);
v_backend_1815_ = lean_ctor_get_uint8(v_cfg_1803_, sizeof(void*)*13 + 1);
v_platformIndependent_1816_ = lean_ctor_get(v_cfg_1803_, 10);
v_dynlibs_1817_ = lean_ctor_get(v_cfg_1803_, 11);
v_plugins_1818_ = lean_ctor_get(v_cfg_1803_, 12);
v_requiresModuleSystem_1819_ = lean_ctor_get_uint8(v_cfg_1803_, sizeof(void*)*13 + 2);
v_allowNonModules_1820_ = lean_ctor_get_uint8(v_cfg_1803_, sizeof(void*)*13 + 3);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_cfg_1803_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1822_ = v_cfg_1803_;
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_plugins_1818_);
lean_inc(v_dynlibs_1817_);
lean_inc(v_platformIndependent_1816_);
lean_inc(v_weakLinkArgs_1814_);
lean_inc(v_moreLinkArgs_1813_);
lean_inc(v_moreLinkLibs_1812_);
lean_inc(v_moreLinkObjs_1811_);
lean_inc(v_weakLeancArgs_1810_);
lean_inc(v_moreServerOptions_1809_);
lean_inc(v_moreLeancArgs_1808_);
lean_inc(v_weakLeanArgs_1807_);
lean_inc(v_moreLeanArgs_1806_);
lean_inc(v_leanOptions_1805_);
lean_dec(v_cfg_1803_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1828_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_apply_1(v_f_1802_, v_weakLinkArgs_1814_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 9, v___x_1824_);
v___x_1826_ = v___x_1822_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_leanOptions_1805_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_moreLeanArgs_1806_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_weakLeanArgs_1807_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_moreLeancArgs_1808_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_moreServerOptions_1809_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_weakLeancArgs_1810_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_moreLinkObjs_1811_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_moreLinkLibs_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_moreLinkArgs_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 9, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1827_, 10, v_platformIndependent_1816_);
lean_ctor_set(v_reuseFailAlloc_1827_, 11, v_dynlibs_1817_);
lean_ctor_set(v_reuseFailAlloc_1827_, 12, v_plugins_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13, v_buildType_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 1, v_backend_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1827_, sizeof(void*)*13 + 3, v_allowNonModules_1820_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1839_){
_start:
{
uint8_t v_backend_1840_; 
v_backend_1840_ = lean_ctor_get_uint8(v_cfg_1839_, sizeof(void*)*13 + 1);
return v_backend_1840_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1841_){
_start:
{
uint8_t v_res_1842_; lean_object* v_r_1843_; 
v_res_1842_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1841_);
lean_dec_ref(v_cfg_1841_);
v_r_1843_ = lean_box(v_res_1842_);
return v_r_1843_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1844_, lean_object* v_cfg_1845_){
_start:
{
uint8_t v_buildType_1846_; lean_object* v_leanOptions_1847_; lean_object* v_moreLeanArgs_1848_; lean_object* v_weakLeanArgs_1849_; lean_object* v_moreLeancArgs_1850_; lean_object* v_moreServerOptions_1851_; lean_object* v_weakLeancArgs_1852_; lean_object* v_moreLinkObjs_1853_; lean_object* v_moreLinkLibs_1854_; lean_object* v_moreLinkArgs_1855_; lean_object* v_weakLinkArgs_1856_; lean_object* v_platformIndependent_1857_; lean_object* v_dynlibs_1858_; lean_object* v_plugins_1859_; uint8_t v_requiresModuleSystem_1860_; uint8_t v_allowNonModules_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v_buildType_1846_ = lean_ctor_get_uint8(v_cfg_1845_, sizeof(void*)*13);
v_leanOptions_1847_ = lean_ctor_get(v_cfg_1845_, 0);
v_moreLeanArgs_1848_ = lean_ctor_get(v_cfg_1845_, 1);
v_weakLeanArgs_1849_ = lean_ctor_get(v_cfg_1845_, 2);
v_moreLeancArgs_1850_ = lean_ctor_get(v_cfg_1845_, 3);
v_moreServerOptions_1851_ = lean_ctor_get(v_cfg_1845_, 4);
v_weakLeancArgs_1852_ = lean_ctor_get(v_cfg_1845_, 5);
v_moreLinkObjs_1853_ = lean_ctor_get(v_cfg_1845_, 6);
v_moreLinkLibs_1854_ = lean_ctor_get(v_cfg_1845_, 7);
v_moreLinkArgs_1855_ = lean_ctor_get(v_cfg_1845_, 8);
v_weakLinkArgs_1856_ = lean_ctor_get(v_cfg_1845_, 9);
v_platformIndependent_1857_ = lean_ctor_get(v_cfg_1845_, 10);
v_dynlibs_1858_ = lean_ctor_get(v_cfg_1845_, 11);
v_plugins_1859_ = lean_ctor_get(v_cfg_1845_, 12);
v_requiresModuleSystem_1860_ = lean_ctor_get_uint8(v_cfg_1845_, sizeof(void*)*13 + 2);
v_allowNonModules_1861_ = lean_ctor_get_uint8(v_cfg_1845_, sizeof(void*)*13 + 3);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_cfg_1845_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v_cfg_1845_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_plugins_1859_);
lean_inc(v_dynlibs_1858_);
lean_inc(v_platformIndependent_1857_);
lean_inc(v_weakLinkArgs_1856_);
lean_inc(v_moreLinkArgs_1855_);
lean_inc(v_moreLinkLibs_1854_);
lean_inc(v_moreLinkObjs_1853_);
lean_inc(v_weakLeancArgs_1852_);
lean_inc(v_moreServerOptions_1851_);
lean_inc(v_moreLeancArgs_1850_);
lean_inc(v_weakLeanArgs_1849_);
lean_inc(v_moreLeanArgs_1848_);
lean_inc(v_leanOptions_1847_);
lean_dec(v_cfg_1845_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_leanOptions_1847_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v_moreLeanArgs_1848_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_weakLeanArgs_1849_);
lean_ctor_set(v_reuseFailAlloc_1867_, 3, v_moreLeancArgs_1850_);
lean_ctor_set(v_reuseFailAlloc_1867_, 4, v_moreServerOptions_1851_);
lean_ctor_set(v_reuseFailAlloc_1867_, 5, v_weakLeancArgs_1852_);
lean_ctor_set(v_reuseFailAlloc_1867_, 6, v_moreLinkObjs_1853_);
lean_ctor_set(v_reuseFailAlloc_1867_, 7, v_moreLinkLibs_1854_);
lean_ctor_set(v_reuseFailAlloc_1867_, 8, v_moreLinkArgs_1855_);
lean_ctor_set(v_reuseFailAlloc_1867_, 9, v_weakLinkArgs_1856_);
lean_ctor_set(v_reuseFailAlloc_1867_, 10, v_platformIndependent_1857_);
lean_ctor_set(v_reuseFailAlloc_1867_, 11, v_dynlibs_1858_);
lean_ctor_set(v_reuseFailAlloc_1867_, 12, v_plugins_1859_);
lean_ctor_set_uint8(v_reuseFailAlloc_1867_, sizeof(void*)*13, v_buildType_1846_);
lean_ctor_set_uint8(v_reuseFailAlloc_1867_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1860_);
lean_ctor_set_uint8(v_reuseFailAlloc_1867_, sizeof(void*)*13 + 3, v_allowNonModules_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_ctor_set_uint8(v___x_1866_, sizeof(void*)*13 + 1, v_val_1844_);
return v___x_1866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1869_, lean_object* v_cfg_1870_){
_start:
{
uint8_t v_val_85__boxed_1871_; lean_object* v_res_1872_; 
v_val_85__boxed_1871_ = lean_unbox(v_val_1869_);
v_res_1872_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_85__boxed_1871_, v_cfg_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1873_, lean_object* v_cfg_1874_){
_start:
{
uint8_t v_buildType_1875_; lean_object* v_leanOptions_1876_; lean_object* v_moreLeanArgs_1877_; lean_object* v_weakLeanArgs_1878_; lean_object* v_moreLeancArgs_1879_; lean_object* v_moreServerOptions_1880_; lean_object* v_weakLeancArgs_1881_; lean_object* v_moreLinkObjs_1882_; lean_object* v_moreLinkLibs_1883_; lean_object* v_moreLinkArgs_1884_; lean_object* v_weakLinkArgs_1885_; uint8_t v_backend_1886_; lean_object* v_platformIndependent_1887_; lean_object* v_dynlibs_1888_; lean_object* v_plugins_1889_; uint8_t v_requiresModuleSystem_1890_; uint8_t v_allowNonModules_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1901_; 
v_buildType_1875_ = lean_ctor_get_uint8(v_cfg_1874_, sizeof(void*)*13);
v_leanOptions_1876_ = lean_ctor_get(v_cfg_1874_, 0);
v_moreLeanArgs_1877_ = lean_ctor_get(v_cfg_1874_, 1);
v_weakLeanArgs_1878_ = lean_ctor_get(v_cfg_1874_, 2);
v_moreLeancArgs_1879_ = lean_ctor_get(v_cfg_1874_, 3);
v_moreServerOptions_1880_ = lean_ctor_get(v_cfg_1874_, 4);
v_weakLeancArgs_1881_ = lean_ctor_get(v_cfg_1874_, 5);
v_moreLinkObjs_1882_ = lean_ctor_get(v_cfg_1874_, 6);
v_moreLinkLibs_1883_ = lean_ctor_get(v_cfg_1874_, 7);
v_moreLinkArgs_1884_ = lean_ctor_get(v_cfg_1874_, 8);
v_weakLinkArgs_1885_ = lean_ctor_get(v_cfg_1874_, 9);
v_backend_1886_ = lean_ctor_get_uint8(v_cfg_1874_, sizeof(void*)*13 + 1);
v_platformIndependent_1887_ = lean_ctor_get(v_cfg_1874_, 10);
v_dynlibs_1888_ = lean_ctor_get(v_cfg_1874_, 11);
v_plugins_1889_ = lean_ctor_get(v_cfg_1874_, 12);
v_requiresModuleSystem_1890_ = lean_ctor_get_uint8(v_cfg_1874_, sizeof(void*)*13 + 2);
v_allowNonModules_1891_ = lean_ctor_get_uint8(v_cfg_1874_, sizeof(void*)*13 + 3);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_cfg_1874_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1893_ = v_cfg_1874_;
v_isShared_1894_ = v_isSharedCheck_1901_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_plugins_1889_);
lean_inc(v_dynlibs_1888_);
lean_inc(v_platformIndependent_1887_);
lean_inc(v_weakLinkArgs_1885_);
lean_inc(v_moreLinkArgs_1884_);
lean_inc(v_moreLinkLibs_1883_);
lean_inc(v_moreLinkObjs_1882_);
lean_inc(v_weakLeancArgs_1881_);
lean_inc(v_moreServerOptions_1880_);
lean_inc(v_moreLeancArgs_1879_);
lean_inc(v_weakLeanArgs_1878_);
lean_inc(v_moreLeanArgs_1877_);
lean_inc(v_leanOptions_1876_);
lean_dec(v_cfg_1874_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1901_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1895_ = lean_box(v_backend_1886_);
v___x_1896_ = lean_apply_1(v_f_1873_, v___x_1895_);
if (v_isShared_1894_ == 0)
{
v___x_1898_ = v___x_1893_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_leanOptions_1876_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v_moreLeanArgs_1877_);
lean_ctor_set(v_reuseFailAlloc_1900_, 2, v_weakLeanArgs_1878_);
lean_ctor_set(v_reuseFailAlloc_1900_, 3, v_moreLeancArgs_1879_);
lean_ctor_set(v_reuseFailAlloc_1900_, 4, v_moreServerOptions_1880_);
lean_ctor_set(v_reuseFailAlloc_1900_, 5, v_weakLeancArgs_1881_);
lean_ctor_set(v_reuseFailAlloc_1900_, 6, v_moreLinkObjs_1882_);
lean_ctor_set(v_reuseFailAlloc_1900_, 7, v_moreLinkLibs_1883_);
lean_ctor_set(v_reuseFailAlloc_1900_, 8, v_moreLinkArgs_1884_);
lean_ctor_set(v_reuseFailAlloc_1900_, 9, v_weakLinkArgs_1885_);
lean_ctor_set(v_reuseFailAlloc_1900_, 10, v_platformIndependent_1887_);
lean_ctor_set(v_reuseFailAlloc_1900_, 11, v_dynlibs_1888_);
lean_ctor_set(v_reuseFailAlloc_1900_, 12, v_plugins_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1900_, sizeof(void*)*13, v_buildType_1875_);
v___x_1898_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
uint8_t v___x_1899_; 
v___x_1899_ = lean_unbox(v___x_1896_);
lean_ctor_set_uint8(v___x_1898_, sizeof(void*)*13 + 1, v___x_1899_);
lean_ctor_set_uint8(v___x_1898_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1890_);
lean_ctor_set_uint8(v___x_1898_, sizeof(void*)*13 + 3, v_allowNonModules_1891_);
return v___x_1898_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1902_){
_start:
{
uint8_t v___x_1903_; 
v___x_1903_ = 2;
return v___x_1903_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1904_){
_start:
{
uint8_t v_res_1905_; lean_object* v_r_1906_; 
v_res_1905_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1904_);
lean_dec_ref(v_x_1904_);
v_r_1906_ = lean_box(v_res_1905_);
return v_r_1906_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1918_){
_start:
{
lean_object* v_platformIndependent_1919_; 
v_platformIndependent_1919_ = lean_ctor_get(v_cfg_1918_, 10);
lean_inc(v_platformIndependent_1919_);
return v_platformIndependent_1919_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1920_);
lean_dec_ref(v_cfg_1920_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1922_, lean_object* v_cfg_1923_){
_start:
{
uint8_t v_buildType_1924_; lean_object* v_leanOptions_1925_; lean_object* v_moreLeanArgs_1926_; lean_object* v_weakLeanArgs_1927_; lean_object* v_moreLeancArgs_1928_; lean_object* v_moreServerOptions_1929_; lean_object* v_weakLeancArgs_1930_; lean_object* v_moreLinkObjs_1931_; lean_object* v_moreLinkLibs_1932_; lean_object* v_moreLinkArgs_1933_; lean_object* v_weakLinkArgs_1934_; uint8_t v_backend_1935_; lean_object* v_dynlibs_1936_; lean_object* v_plugins_1937_; uint8_t v_requiresModuleSystem_1938_; uint8_t v_allowNonModules_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
v_buildType_1924_ = lean_ctor_get_uint8(v_cfg_1923_, sizeof(void*)*13);
v_leanOptions_1925_ = lean_ctor_get(v_cfg_1923_, 0);
v_moreLeanArgs_1926_ = lean_ctor_get(v_cfg_1923_, 1);
v_weakLeanArgs_1927_ = lean_ctor_get(v_cfg_1923_, 2);
v_moreLeancArgs_1928_ = lean_ctor_get(v_cfg_1923_, 3);
v_moreServerOptions_1929_ = lean_ctor_get(v_cfg_1923_, 4);
v_weakLeancArgs_1930_ = lean_ctor_get(v_cfg_1923_, 5);
v_moreLinkObjs_1931_ = lean_ctor_get(v_cfg_1923_, 6);
v_moreLinkLibs_1932_ = lean_ctor_get(v_cfg_1923_, 7);
v_moreLinkArgs_1933_ = lean_ctor_get(v_cfg_1923_, 8);
v_weakLinkArgs_1934_ = lean_ctor_get(v_cfg_1923_, 9);
v_backend_1935_ = lean_ctor_get_uint8(v_cfg_1923_, sizeof(void*)*13 + 1);
v_dynlibs_1936_ = lean_ctor_get(v_cfg_1923_, 11);
v_plugins_1937_ = lean_ctor_get(v_cfg_1923_, 12);
v_requiresModuleSystem_1938_ = lean_ctor_get_uint8(v_cfg_1923_, sizeof(void*)*13 + 2);
v_allowNonModules_1939_ = lean_ctor_get_uint8(v_cfg_1923_, sizeof(void*)*13 + 3);
v_isSharedCheck_1946_ = !lean_is_exclusive(v_cfg_1923_);
if (v_isSharedCheck_1946_ == 0)
{
lean_object* v_unused_1947_; 
v_unused_1947_ = lean_ctor_get(v_cfg_1923_, 10);
lean_dec(v_unused_1947_);
v___x_1941_ = v_cfg_1923_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_plugins_1937_);
lean_inc(v_dynlibs_1936_);
lean_inc(v_weakLinkArgs_1934_);
lean_inc(v_moreLinkArgs_1933_);
lean_inc(v_moreLinkLibs_1932_);
lean_inc(v_moreLinkObjs_1931_);
lean_inc(v_weakLeancArgs_1930_);
lean_inc(v_moreServerOptions_1929_);
lean_inc(v_moreLeancArgs_1928_);
lean_inc(v_weakLeanArgs_1927_);
lean_inc(v_moreLeanArgs_1926_);
lean_inc(v_leanOptions_1925_);
lean_dec(v_cfg_1923_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 10, v_val_1922_);
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_leanOptions_1925_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_moreLeanArgs_1926_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v_weakLeanArgs_1927_);
lean_ctor_set(v_reuseFailAlloc_1945_, 3, v_moreLeancArgs_1928_);
lean_ctor_set(v_reuseFailAlloc_1945_, 4, v_moreServerOptions_1929_);
lean_ctor_set(v_reuseFailAlloc_1945_, 5, v_weakLeancArgs_1930_);
lean_ctor_set(v_reuseFailAlloc_1945_, 6, v_moreLinkObjs_1931_);
lean_ctor_set(v_reuseFailAlloc_1945_, 7, v_moreLinkLibs_1932_);
lean_ctor_set(v_reuseFailAlloc_1945_, 8, v_moreLinkArgs_1933_);
lean_ctor_set(v_reuseFailAlloc_1945_, 9, v_weakLinkArgs_1934_);
lean_ctor_set(v_reuseFailAlloc_1945_, 10, v_val_1922_);
lean_ctor_set(v_reuseFailAlloc_1945_, 11, v_dynlibs_1936_);
lean_ctor_set(v_reuseFailAlloc_1945_, 12, v_plugins_1937_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*13, v_buildType_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*13 + 1, v_backend_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1938_);
lean_ctor_set_uint8(v_reuseFailAlloc_1945_, sizeof(void*)*13 + 3, v_allowNonModules_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_1948_, lean_object* v_cfg_1949_){
_start:
{
uint8_t v_buildType_1950_; lean_object* v_leanOptions_1951_; lean_object* v_moreLeanArgs_1952_; lean_object* v_weakLeanArgs_1953_; lean_object* v_moreLeancArgs_1954_; lean_object* v_moreServerOptions_1955_; lean_object* v_weakLeancArgs_1956_; lean_object* v_moreLinkObjs_1957_; lean_object* v_moreLinkLibs_1958_; lean_object* v_moreLinkArgs_1959_; lean_object* v_weakLinkArgs_1960_; uint8_t v_backend_1961_; lean_object* v_platformIndependent_1962_; lean_object* v_dynlibs_1963_; lean_object* v_plugins_1964_; uint8_t v_requiresModuleSystem_1965_; uint8_t v_allowNonModules_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1974_; 
v_buildType_1950_ = lean_ctor_get_uint8(v_cfg_1949_, sizeof(void*)*13);
v_leanOptions_1951_ = lean_ctor_get(v_cfg_1949_, 0);
v_moreLeanArgs_1952_ = lean_ctor_get(v_cfg_1949_, 1);
v_weakLeanArgs_1953_ = lean_ctor_get(v_cfg_1949_, 2);
v_moreLeancArgs_1954_ = lean_ctor_get(v_cfg_1949_, 3);
v_moreServerOptions_1955_ = lean_ctor_get(v_cfg_1949_, 4);
v_weakLeancArgs_1956_ = lean_ctor_get(v_cfg_1949_, 5);
v_moreLinkObjs_1957_ = lean_ctor_get(v_cfg_1949_, 6);
v_moreLinkLibs_1958_ = lean_ctor_get(v_cfg_1949_, 7);
v_moreLinkArgs_1959_ = lean_ctor_get(v_cfg_1949_, 8);
v_weakLinkArgs_1960_ = lean_ctor_get(v_cfg_1949_, 9);
v_backend_1961_ = lean_ctor_get_uint8(v_cfg_1949_, sizeof(void*)*13 + 1);
v_platformIndependent_1962_ = lean_ctor_get(v_cfg_1949_, 10);
v_dynlibs_1963_ = lean_ctor_get(v_cfg_1949_, 11);
v_plugins_1964_ = lean_ctor_get(v_cfg_1949_, 12);
v_requiresModuleSystem_1965_ = lean_ctor_get_uint8(v_cfg_1949_, sizeof(void*)*13 + 2);
v_allowNonModules_1966_ = lean_ctor_get_uint8(v_cfg_1949_, sizeof(void*)*13 + 3);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_cfg_1949_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1968_ = v_cfg_1949_;
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_plugins_1964_);
lean_inc(v_dynlibs_1963_);
lean_inc(v_platformIndependent_1962_);
lean_inc(v_weakLinkArgs_1960_);
lean_inc(v_moreLinkArgs_1959_);
lean_inc(v_moreLinkLibs_1958_);
lean_inc(v_moreLinkObjs_1957_);
lean_inc(v_weakLeancArgs_1956_);
lean_inc(v_moreServerOptions_1955_);
lean_inc(v_moreLeancArgs_1954_);
lean_inc(v_weakLeanArgs_1953_);
lean_inc(v_moreLeanArgs_1952_);
lean_inc(v_leanOptions_1951_);
lean_dec(v_cfg_1949_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1974_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1970_ = lean_apply_1(v_f_1948_, v_platformIndependent_1962_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 10, v___x_1970_);
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_leanOptions_1951_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_moreLeanArgs_1952_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_weakLeanArgs_1953_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_moreLeancArgs_1954_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_moreServerOptions_1955_);
lean_ctor_set(v_reuseFailAlloc_1973_, 5, v_weakLeancArgs_1956_);
lean_ctor_set(v_reuseFailAlloc_1973_, 6, v_moreLinkObjs_1957_);
lean_ctor_set(v_reuseFailAlloc_1973_, 7, v_moreLinkLibs_1958_);
lean_ctor_set(v_reuseFailAlloc_1973_, 8, v_moreLinkArgs_1959_);
lean_ctor_set(v_reuseFailAlloc_1973_, 9, v_weakLinkArgs_1960_);
lean_ctor_set(v_reuseFailAlloc_1973_, 10, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1973_, 11, v_dynlibs_1963_);
lean_ctor_set(v_reuseFailAlloc_1973_, 12, v_plugins_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*13, v_buildType_1950_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*13 + 1, v_backend_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*13 + 2, v_requiresModuleSystem_1965_);
lean_ctor_set_uint8(v_reuseFailAlloc_1973_, sizeof(void*)*13 + 3, v_allowNonModules_1966_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_1975_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_box(0);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_1977_);
lean_dec_ref(v_x_1977_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_1990_){
_start:
{
lean_object* v_dynlibs_1991_; 
v_dynlibs_1991_ = lean_ctor_get(v_cfg_1990_, 11);
lean_inc_ref(v_dynlibs_1991_);
return v_dynlibs_1991_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_1992_);
lean_dec_ref(v_cfg_1992_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_1994_, lean_object* v_cfg_1995_){
_start:
{
uint8_t v_buildType_1996_; lean_object* v_leanOptions_1997_; lean_object* v_moreLeanArgs_1998_; lean_object* v_weakLeanArgs_1999_; lean_object* v_moreLeancArgs_2000_; lean_object* v_moreServerOptions_2001_; lean_object* v_weakLeancArgs_2002_; lean_object* v_moreLinkObjs_2003_; lean_object* v_moreLinkLibs_2004_; lean_object* v_moreLinkArgs_2005_; lean_object* v_weakLinkArgs_2006_; uint8_t v_backend_2007_; lean_object* v_platformIndependent_2008_; lean_object* v_plugins_2009_; uint8_t v_requiresModuleSystem_2010_; uint8_t v_allowNonModules_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v_buildType_1996_ = lean_ctor_get_uint8(v_cfg_1995_, sizeof(void*)*13);
v_leanOptions_1997_ = lean_ctor_get(v_cfg_1995_, 0);
v_moreLeanArgs_1998_ = lean_ctor_get(v_cfg_1995_, 1);
v_weakLeanArgs_1999_ = lean_ctor_get(v_cfg_1995_, 2);
v_moreLeancArgs_2000_ = lean_ctor_get(v_cfg_1995_, 3);
v_moreServerOptions_2001_ = lean_ctor_get(v_cfg_1995_, 4);
v_weakLeancArgs_2002_ = lean_ctor_get(v_cfg_1995_, 5);
v_moreLinkObjs_2003_ = lean_ctor_get(v_cfg_1995_, 6);
v_moreLinkLibs_2004_ = lean_ctor_get(v_cfg_1995_, 7);
v_moreLinkArgs_2005_ = lean_ctor_get(v_cfg_1995_, 8);
v_weakLinkArgs_2006_ = lean_ctor_get(v_cfg_1995_, 9);
v_backend_2007_ = lean_ctor_get_uint8(v_cfg_1995_, sizeof(void*)*13 + 1);
v_platformIndependent_2008_ = lean_ctor_get(v_cfg_1995_, 10);
v_plugins_2009_ = lean_ctor_get(v_cfg_1995_, 12);
v_requiresModuleSystem_2010_ = lean_ctor_get_uint8(v_cfg_1995_, sizeof(void*)*13 + 2);
v_allowNonModules_2011_ = lean_ctor_get_uint8(v_cfg_1995_, sizeof(void*)*13 + 3);
v_isSharedCheck_2018_ = !lean_is_exclusive(v_cfg_1995_);
if (v_isSharedCheck_2018_ == 0)
{
lean_object* v_unused_2019_; 
v_unused_2019_ = lean_ctor_get(v_cfg_1995_, 11);
lean_dec(v_unused_2019_);
v___x_2013_ = v_cfg_1995_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_plugins_2009_);
lean_inc(v_platformIndependent_2008_);
lean_inc(v_weakLinkArgs_2006_);
lean_inc(v_moreLinkArgs_2005_);
lean_inc(v_moreLinkLibs_2004_);
lean_inc(v_moreLinkObjs_2003_);
lean_inc(v_weakLeancArgs_2002_);
lean_inc(v_moreServerOptions_2001_);
lean_inc(v_moreLeancArgs_2000_);
lean_inc(v_weakLeanArgs_1999_);
lean_inc(v_moreLeanArgs_1998_);
lean_inc(v_leanOptions_1997_);
lean_dec(v_cfg_1995_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 11, v_val_1994_);
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_leanOptions_1997_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_moreLeanArgs_1998_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_weakLeanArgs_1999_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_moreLeancArgs_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 4, v_moreServerOptions_2001_);
lean_ctor_set(v_reuseFailAlloc_2017_, 5, v_weakLeancArgs_2002_);
lean_ctor_set(v_reuseFailAlloc_2017_, 6, v_moreLinkObjs_2003_);
lean_ctor_set(v_reuseFailAlloc_2017_, 7, v_moreLinkLibs_2004_);
lean_ctor_set(v_reuseFailAlloc_2017_, 8, v_moreLinkArgs_2005_);
lean_ctor_set(v_reuseFailAlloc_2017_, 9, v_weakLinkArgs_2006_);
lean_ctor_set(v_reuseFailAlloc_2017_, 10, v_platformIndependent_2008_);
lean_ctor_set(v_reuseFailAlloc_2017_, 11, v_val_1994_);
lean_ctor_set(v_reuseFailAlloc_2017_, 12, v_plugins_2009_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13, v_buildType_1996_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 1, v_backend_2007_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2010_);
lean_ctor_set_uint8(v_reuseFailAlloc_2017_, sizeof(void*)*13 + 3, v_allowNonModules_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_2020_, lean_object* v_cfg_2021_){
_start:
{
uint8_t v_buildType_2022_; lean_object* v_leanOptions_2023_; lean_object* v_moreLeanArgs_2024_; lean_object* v_weakLeanArgs_2025_; lean_object* v_moreLeancArgs_2026_; lean_object* v_moreServerOptions_2027_; lean_object* v_weakLeancArgs_2028_; lean_object* v_moreLinkObjs_2029_; lean_object* v_moreLinkLibs_2030_; lean_object* v_moreLinkArgs_2031_; lean_object* v_weakLinkArgs_2032_; uint8_t v_backend_2033_; lean_object* v_platformIndependent_2034_; lean_object* v_dynlibs_2035_; lean_object* v_plugins_2036_; uint8_t v_requiresModuleSystem_2037_; uint8_t v_allowNonModules_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2046_; 
v_buildType_2022_ = lean_ctor_get_uint8(v_cfg_2021_, sizeof(void*)*13);
v_leanOptions_2023_ = lean_ctor_get(v_cfg_2021_, 0);
v_moreLeanArgs_2024_ = lean_ctor_get(v_cfg_2021_, 1);
v_weakLeanArgs_2025_ = lean_ctor_get(v_cfg_2021_, 2);
v_moreLeancArgs_2026_ = lean_ctor_get(v_cfg_2021_, 3);
v_moreServerOptions_2027_ = lean_ctor_get(v_cfg_2021_, 4);
v_weakLeancArgs_2028_ = lean_ctor_get(v_cfg_2021_, 5);
v_moreLinkObjs_2029_ = lean_ctor_get(v_cfg_2021_, 6);
v_moreLinkLibs_2030_ = lean_ctor_get(v_cfg_2021_, 7);
v_moreLinkArgs_2031_ = lean_ctor_get(v_cfg_2021_, 8);
v_weakLinkArgs_2032_ = lean_ctor_get(v_cfg_2021_, 9);
v_backend_2033_ = lean_ctor_get_uint8(v_cfg_2021_, sizeof(void*)*13 + 1);
v_platformIndependent_2034_ = lean_ctor_get(v_cfg_2021_, 10);
v_dynlibs_2035_ = lean_ctor_get(v_cfg_2021_, 11);
v_plugins_2036_ = lean_ctor_get(v_cfg_2021_, 12);
v_requiresModuleSystem_2037_ = lean_ctor_get_uint8(v_cfg_2021_, sizeof(void*)*13 + 2);
v_allowNonModules_2038_ = lean_ctor_get_uint8(v_cfg_2021_, sizeof(void*)*13 + 3);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_cfg_2021_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2040_ = v_cfg_2021_;
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_plugins_2036_);
lean_inc(v_dynlibs_2035_);
lean_inc(v_platformIndependent_2034_);
lean_inc(v_weakLinkArgs_2032_);
lean_inc(v_moreLinkArgs_2031_);
lean_inc(v_moreLinkLibs_2030_);
lean_inc(v_moreLinkObjs_2029_);
lean_inc(v_weakLeancArgs_2028_);
lean_inc(v_moreServerOptions_2027_);
lean_inc(v_moreLeancArgs_2026_);
lean_inc(v_weakLeanArgs_2025_);
lean_inc(v_moreLeanArgs_2024_);
lean_inc(v_leanOptions_2023_);
lean_dec(v_cfg_2021_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2046_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_apply_1(v_f_2020_, v_dynlibs_2035_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 11, v___x_2042_);
v___x_2044_ = v___x_2040_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_leanOptions_2023_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_moreLeanArgs_2024_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_weakLeanArgs_2025_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_moreLeancArgs_2026_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_moreServerOptions_2027_);
lean_ctor_set(v_reuseFailAlloc_2045_, 5, v_weakLeancArgs_2028_);
lean_ctor_set(v_reuseFailAlloc_2045_, 6, v_moreLinkObjs_2029_);
lean_ctor_set(v_reuseFailAlloc_2045_, 7, v_moreLinkLibs_2030_);
lean_ctor_set(v_reuseFailAlloc_2045_, 8, v_moreLinkArgs_2031_);
lean_ctor_set(v_reuseFailAlloc_2045_, 9, v_weakLinkArgs_2032_);
lean_ctor_set(v_reuseFailAlloc_2045_, 10, v_platformIndependent_2034_);
lean_ctor_set(v_reuseFailAlloc_2045_, 11, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2045_, 12, v_plugins_2036_);
lean_ctor_set_uint8(v_reuseFailAlloc_2045_, sizeof(void*)*13, v_buildType_2022_);
lean_ctor_set_uint8(v_reuseFailAlloc_2045_, sizeof(void*)*13 + 1, v_backend_2033_);
lean_ctor_set_uint8(v_reuseFailAlloc_2045_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2037_);
lean_ctor_set_uint8(v_reuseFailAlloc_2045_, sizeof(void*)*13 + 3, v_allowNonModules_2038_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_2057_){
_start:
{
lean_object* v_plugins_2058_; 
v_plugins_2058_ = lean_ctor_get(v_cfg_2057_, 12);
lean_inc_ref(v_plugins_2058_);
return v_plugins_2058_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_2059_);
lean_dec_ref(v_cfg_2059_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_2061_, lean_object* v_cfg_2062_){
_start:
{
uint8_t v_buildType_2063_; lean_object* v_leanOptions_2064_; lean_object* v_moreLeanArgs_2065_; lean_object* v_weakLeanArgs_2066_; lean_object* v_moreLeancArgs_2067_; lean_object* v_moreServerOptions_2068_; lean_object* v_weakLeancArgs_2069_; lean_object* v_moreLinkObjs_2070_; lean_object* v_moreLinkLibs_2071_; lean_object* v_moreLinkArgs_2072_; lean_object* v_weakLinkArgs_2073_; uint8_t v_backend_2074_; lean_object* v_platformIndependent_2075_; lean_object* v_dynlibs_2076_; uint8_t v_requiresModuleSystem_2077_; uint8_t v_allowNonModules_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
v_buildType_2063_ = lean_ctor_get_uint8(v_cfg_2062_, sizeof(void*)*13);
v_leanOptions_2064_ = lean_ctor_get(v_cfg_2062_, 0);
v_moreLeanArgs_2065_ = lean_ctor_get(v_cfg_2062_, 1);
v_weakLeanArgs_2066_ = lean_ctor_get(v_cfg_2062_, 2);
v_moreLeancArgs_2067_ = lean_ctor_get(v_cfg_2062_, 3);
v_moreServerOptions_2068_ = lean_ctor_get(v_cfg_2062_, 4);
v_weakLeancArgs_2069_ = lean_ctor_get(v_cfg_2062_, 5);
v_moreLinkObjs_2070_ = lean_ctor_get(v_cfg_2062_, 6);
v_moreLinkLibs_2071_ = lean_ctor_get(v_cfg_2062_, 7);
v_moreLinkArgs_2072_ = lean_ctor_get(v_cfg_2062_, 8);
v_weakLinkArgs_2073_ = lean_ctor_get(v_cfg_2062_, 9);
v_backend_2074_ = lean_ctor_get_uint8(v_cfg_2062_, sizeof(void*)*13 + 1);
v_platformIndependent_2075_ = lean_ctor_get(v_cfg_2062_, 10);
v_dynlibs_2076_ = lean_ctor_get(v_cfg_2062_, 11);
v_requiresModuleSystem_2077_ = lean_ctor_get_uint8(v_cfg_2062_, sizeof(void*)*13 + 2);
v_allowNonModules_2078_ = lean_ctor_get_uint8(v_cfg_2062_, sizeof(void*)*13 + 3);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_cfg_2062_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v_cfg_2062_, 12);
lean_dec(v_unused_2086_);
v___x_2080_ = v_cfg_2062_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_dynlibs_2076_);
lean_inc(v_platformIndependent_2075_);
lean_inc(v_weakLinkArgs_2073_);
lean_inc(v_moreLinkArgs_2072_);
lean_inc(v_moreLinkLibs_2071_);
lean_inc(v_moreLinkObjs_2070_);
lean_inc(v_weakLeancArgs_2069_);
lean_inc(v_moreServerOptions_2068_);
lean_inc(v_moreLeancArgs_2067_);
lean_inc(v_weakLeanArgs_2066_);
lean_inc(v_moreLeanArgs_2065_);
lean_inc(v_leanOptions_2064_);
lean_dec(v_cfg_2062_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 12, v_val_2061_);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_leanOptions_2064_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_moreLeanArgs_2065_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_weakLeanArgs_2066_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_moreLeancArgs_2067_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_moreServerOptions_2068_);
lean_ctor_set(v_reuseFailAlloc_2084_, 5, v_weakLeancArgs_2069_);
lean_ctor_set(v_reuseFailAlloc_2084_, 6, v_moreLinkObjs_2070_);
lean_ctor_set(v_reuseFailAlloc_2084_, 7, v_moreLinkLibs_2071_);
lean_ctor_set(v_reuseFailAlloc_2084_, 8, v_moreLinkArgs_2072_);
lean_ctor_set(v_reuseFailAlloc_2084_, 9, v_weakLinkArgs_2073_);
lean_ctor_set(v_reuseFailAlloc_2084_, 10, v_platformIndependent_2075_);
lean_ctor_set(v_reuseFailAlloc_2084_, 11, v_dynlibs_2076_);
lean_ctor_set(v_reuseFailAlloc_2084_, 12, v_val_2061_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*13, v_buildType_2063_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*13 + 1, v_backend_2074_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2077_);
lean_ctor_set_uint8(v_reuseFailAlloc_2084_, sizeof(void*)*13 + 3, v_allowNonModules_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_2087_, lean_object* v_cfg_2088_){
_start:
{
uint8_t v_buildType_2089_; lean_object* v_leanOptions_2090_; lean_object* v_moreLeanArgs_2091_; lean_object* v_weakLeanArgs_2092_; lean_object* v_moreLeancArgs_2093_; lean_object* v_moreServerOptions_2094_; lean_object* v_weakLeancArgs_2095_; lean_object* v_moreLinkObjs_2096_; lean_object* v_moreLinkLibs_2097_; lean_object* v_moreLinkArgs_2098_; lean_object* v_weakLinkArgs_2099_; uint8_t v_backend_2100_; lean_object* v_platformIndependent_2101_; lean_object* v_dynlibs_2102_; lean_object* v_plugins_2103_; uint8_t v_requiresModuleSystem_2104_; uint8_t v_allowNonModules_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2113_; 
v_buildType_2089_ = lean_ctor_get_uint8(v_cfg_2088_, sizeof(void*)*13);
v_leanOptions_2090_ = lean_ctor_get(v_cfg_2088_, 0);
v_moreLeanArgs_2091_ = lean_ctor_get(v_cfg_2088_, 1);
v_weakLeanArgs_2092_ = lean_ctor_get(v_cfg_2088_, 2);
v_moreLeancArgs_2093_ = lean_ctor_get(v_cfg_2088_, 3);
v_moreServerOptions_2094_ = lean_ctor_get(v_cfg_2088_, 4);
v_weakLeancArgs_2095_ = lean_ctor_get(v_cfg_2088_, 5);
v_moreLinkObjs_2096_ = lean_ctor_get(v_cfg_2088_, 6);
v_moreLinkLibs_2097_ = lean_ctor_get(v_cfg_2088_, 7);
v_moreLinkArgs_2098_ = lean_ctor_get(v_cfg_2088_, 8);
v_weakLinkArgs_2099_ = lean_ctor_get(v_cfg_2088_, 9);
v_backend_2100_ = lean_ctor_get_uint8(v_cfg_2088_, sizeof(void*)*13 + 1);
v_platformIndependent_2101_ = lean_ctor_get(v_cfg_2088_, 10);
v_dynlibs_2102_ = lean_ctor_get(v_cfg_2088_, 11);
v_plugins_2103_ = lean_ctor_get(v_cfg_2088_, 12);
v_requiresModuleSystem_2104_ = lean_ctor_get_uint8(v_cfg_2088_, sizeof(void*)*13 + 2);
v_allowNonModules_2105_ = lean_ctor_get_uint8(v_cfg_2088_, sizeof(void*)*13 + 3);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_cfg_2088_);
if (v_isSharedCheck_2113_ == 0)
{
v___x_2107_ = v_cfg_2088_;
v_isShared_2108_ = v_isSharedCheck_2113_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_plugins_2103_);
lean_inc(v_dynlibs_2102_);
lean_inc(v_platformIndependent_2101_);
lean_inc(v_weakLinkArgs_2099_);
lean_inc(v_moreLinkArgs_2098_);
lean_inc(v_moreLinkLibs_2097_);
lean_inc(v_moreLinkObjs_2096_);
lean_inc(v_weakLeancArgs_2095_);
lean_inc(v_moreServerOptions_2094_);
lean_inc(v_moreLeancArgs_2093_);
lean_inc(v_weakLeanArgs_2092_);
lean_inc(v_moreLeanArgs_2091_);
lean_inc(v_leanOptions_2090_);
lean_dec(v_cfg_2088_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2113_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2111_; 
v___x_2109_ = lean_apply_1(v_f_2087_, v_plugins_2103_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 12, v___x_2109_);
v___x_2111_ = v___x_2107_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_leanOptions_2090_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_moreLeanArgs_2091_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_weakLeanArgs_2092_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_moreLeancArgs_2093_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_moreServerOptions_2094_);
lean_ctor_set(v_reuseFailAlloc_2112_, 5, v_weakLeancArgs_2095_);
lean_ctor_set(v_reuseFailAlloc_2112_, 6, v_moreLinkObjs_2096_);
lean_ctor_set(v_reuseFailAlloc_2112_, 7, v_moreLinkLibs_2097_);
lean_ctor_set(v_reuseFailAlloc_2112_, 8, v_moreLinkArgs_2098_);
lean_ctor_set(v_reuseFailAlloc_2112_, 9, v_weakLinkArgs_2099_);
lean_ctor_set(v_reuseFailAlloc_2112_, 10, v_platformIndependent_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 11, v_dynlibs_2102_);
lean_ctor_set(v_reuseFailAlloc_2112_, 12, v___x_2109_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13, v_buildType_2089_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 1, v_backend_2100_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2104_);
lean_ctor_set_uint8(v_reuseFailAlloc_2112_, sizeof(void*)*13 + 3, v_allowNonModules_2105_);
v___x_2111_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
return v___x_2111_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(lean_object* v_cfg_2124_){
_start:
{
uint8_t v_requiresModuleSystem_2125_; 
v_requiresModuleSystem_2125_ = lean_ctor_get_uint8(v_cfg_2124_, sizeof(void*)*13 + 2);
return v_requiresModuleSystem_2125_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0___boxed(lean_object* v_cfg_2126_){
_start:
{
uint8_t v_res_2127_; lean_object* v_r_2128_; 
v_res_2127_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__0(v_cfg_2126_);
lean_dec_ref(v_cfg_2126_);
v_r_2128_ = lean_box(v_res_2127_);
return v_r_2128_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(uint8_t v_val_2129_, lean_object* v_cfg_2130_){
_start:
{
uint8_t v_buildType_2131_; lean_object* v_leanOptions_2132_; lean_object* v_moreLeanArgs_2133_; lean_object* v_weakLeanArgs_2134_; lean_object* v_moreLeancArgs_2135_; lean_object* v_moreServerOptions_2136_; lean_object* v_weakLeancArgs_2137_; lean_object* v_moreLinkObjs_2138_; lean_object* v_moreLinkLibs_2139_; lean_object* v_moreLinkArgs_2140_; lean_object* v_weakLinkArgs_2141_; uint8_t v_backend_2142_; lean_object* v_platformIndependent_2143_; lean_object* v_dynlibs_2144_; lean_object* v_plugins_2145_; uint8_t v_allowNonModules_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
v_buildType_2131_ = lean_ctor_get_uint8(v_cfg_2130_, sizeof(void*)*13);
v_leanOptions_2132_ = lean_ctor_get(v_cfg_2130_, 0);
v_moreLeanArgs_2133_ = lean_ctor_get(v_cfg_2130_, 1);
v_weakLeanArgs_2134_ = lean_ctor_get(v_cfg_2130_, 2);
v_moreLeancArgs_2135_ = lean_ctor_get(v_cfg_2130_, 3);
v_moreServerOptions_2136_ = lean_ctor_get(v_cfg_2130_, 4);
v_weakLeancArgs_2137_ = lean_ctor_get(v_cfg_2130_, 5);
v_moreLinkObjs_2138_ = lean_ctor_get(v_cfg_2130_, 6);
v_moreLinkLibs_2139_ = lean_ctor_get(v_cfg_2130_, 7);
v_moreLinkArgs_2140_ = lean_ctor_get(v_cfg_2130_, 8);
v_weakLinkArgs_2141_ = lean_ctor_get(v_cfg_2130_, 9);
v_backend_2142_ = lean_ctor_get_uint8(v_cfg_2130_, sizeof(void*)*13 + 1);
v_platformIndependent_2143_ = lean_ctor_get(v_cfg_2130_, 10);
v_dynlibs_2144_ = lean_ctor_get(v_cfg_2130_, 11);
v_plugins_2145_ = lean_ctor_get(v_cfg_2130_, 12);
v_allowNonModules_2146_ = lean_ctor_get_uint8(v_cfg_2130_, sizeof(void*)*13 + 3);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_cfg_2130_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v_cfg_2130_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_plugins_2145_);
lean_inc(v_dynlibs_2144_);
lean_inc(v_platformIndependent_2143_);
lean_inc(v_weakLinkArgs_2141_);
lean_inc(v_moreLinkArgs_2140_);
lean_inc(v_moreLinkLibs_2139_);
lean_inc(v_moreLinkObjs_2138_);
lean_inc(v_weakLeancArgs_2137_);
lean_inc(v_moreServerOptions_2136_);
lean_inc(v_moreLeancArgs_2135_);
lean_inc(v_weakLeanArgs_2134_);
lean_inc(v_moreLeanArgs_2133_);
lean_inc(v_leanOptions_2132_);
lean_dec(v_cfg_2130_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_leanOptions_2132_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v_moreLeanArgs_2133_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_weakLeanArgs_2134_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_moreLeancArgs_2135_);
lean_ctor_set(v_reuseFailAlloc_2152_, 4, v_moreServerOptions_2136_);
lean_ctor_set(v_reuseFailAlloc_2152_, 5, v_weakLeancArgs_2137_);
lean_ctor_set(v_reuseFailAlloc_2152_, 6, v_moreLinkObjs_2138_);
lean_ctor_set(v_reuseFailAlloc_2152_, 7, v_moreLinkLibs_2139_);
lean_ctor_set(v_reuseFailAlloc_2152_, 8, v_moreLinkArgs_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 9, v_weakLinkArgs_2141_);
lean_ctor_set(v_reuseFailAlloc_2152_, 10, v_platformIndependent_2143_);
lean_ctor_set(v_reuseFailAlloc_2152_, 11, v_dynlibs_2144_);
lean_ctor_set(v_reuseFailAlloc_2152_, 12, v_plugins_2145_);
lean_ctor_set_uint8(v_reuseFailAlloc_2152_, sizeof(void*)*13, v_buildType_2131_);
lean_ctor_set_uint8(v_reuseFailAlloc_2152_, sizeof(void*)*13 + 1, v_backend_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2152_, sizeof(void*)*13 + 3, v_allowNonModules_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_ctor_set_uint8(v___x_2151_, sizeof(void*)*13 + 2, v_val_2129_);
return v___x_2151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1___boxed(lean_object* v_val_2154_, lean_object* v_cfg_2155_){
_start:
{
uint8_t v_val_85__boxed_2156_; lean_object* v_res_2157_; 
v_val_85__boxed_2156_ = lean_unbox(v_val_2154_);
v_res_2157_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__1(v_val_85__boxed_2156_, v_cfg_2155_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__2(lean_object* v_f_2158_, lean_object* v_cfg_2159_){
_start:
{
uint8_t v_buildType_2160_; lean_object* v_leanOptions_2161_; lean_object* v_moreLeanArgs_2162_; lean_object* v_weakLeanArgs_2163_; lean_object* v_moreLeancArgs_2164_; lean_object* v_moreServerOptions_2165_; lean_object* v_weakLeancArgs_2166_; lean_object* v_moreLinkObjs_2167_; lean_object* v_moreLinkLibs_2168_; lean_object* v_moreLinkArgs_2169_; lean_object* v_weakLinkArgs_2170_; uint8_t v_backend_2171_; lean_object* v_platformIndependent_2172_; lean_object* v_dynlibs_2173_; lean_object* v_plugins_2174_; uint8_t v_requiresModuleSystem_2175_; uint8_t v_allowNonModules_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2186_; 
v_buildType_2160_ = lean_ctor_get_uint8(v_cfg_2159_, sizeof(void*)*13);
v_leanOptions_2161_ = lean_ctor_get(v_cfg_2159_, 0);
v_moreLeanArgs_2162_ = lean_ctor_get(v_cfg_2159_, 1);
v_weakLeanArgs_2163_ = lean_ctor_get(v_cfg_2159_, 2);
v_moreLeancArgs_2164_ = lean_ctor_get(v_cfg_2159_, 3);
v_moreServerOptions_2165_ = lean_ctor_get(v_cfg_2159_, 4);
v_weakLeancArgs_2166_ = lean_ctor_get(v_cfg_2159_, 5);
v_moreLinkObjs_2167_ = lean_ctor_get(v_cfg_2159_, 6);
v_moreLinkLibs_2168_ = lean_ctor_get(v_cfg_2159_, 7);
v_moreLinkArgs_2169_ = lean_ctor_get(v_cfg_2159_, 8);
v_weakLinkArgs_2170_ = lean_ctor_get(v_cfg_2159_, 9);
v_backend_2171_ = lean_ctor_get_uint8(v_cfg_2159_, sizeof(void*)*13 + 1);
v_platformIndependent_2172_ = lean_ctor_get(v_cfg_2159_, 10);
v_dynlibs_2173_ = lean_ctor_get(v_cfg_2159_, 11);
v_plugins_2174_ = lean_ctor_get(v_cfg_2159_, 12);
v_requiresModuleSystem_2175_ = lean_ctor_get_uint8(v_cfg_2159_, sizeof(void*)*13 + 2);
v_allowNonModules_2176_ = lean_ctor_get_uint8(v_cfg_2159_, sizeof(void*)*13 + 3);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_cfg_2159_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2178_ = v_cfg_2159_;
v_isShared_2179_ = v_isSharedCheck_2186_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_plugins_2174_);
lean_inc(v_dynlibs_2173_);
lean_inc(v_platformIndependent_2172_);
lean_inc(v_weakLinkArgs_2170_);
lean_inc(v_moreLinkArgs_2169_);
lean_inc(v_moreLinkLibs_2168_);
lean_inc(v_moreLinkObjs_2167_);
lean_inc(v_weakLeancArgs_2166_);
lean_inc(v_moreServerOptions_2165_);
lean_inc(v_moreLeancArgs_2164_);
lean_inc(v_weakLeanArgs_2163_);
lean_inc(v_moreLeanArgs_2162_);
lean_inc(v_leanOptions_2161_);
lean_dec(v_cfg_2159_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2186_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2180_ = lean_box(v_requiresModuleSystem_2175_);
v___x_2181_ = lean_apply_1(v_f_2158_, v___x_2180_);
if (v_isShared_2179_ == 0)
{
v___x_2183_ = v___x_2178_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_leanOptions_2161_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_moreLeanArgs_2162_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_weakLeanArgs_2163_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_moreLeancArgs_2164_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v_moreServerOptions_2165_);
lean_ctor_set(v_reuseFailAlloc_2185_, 5, v_weakLeancArgs_2166_);
lean_ctor_set(v_reuseFailAlloc_2185_, 6, v_moreLinkObjs_2167_);
lean_ctor_set(v_reuseFailAlloc_2185_, 7, v_moreLinkLibs_2168_);
lean_ctor_set(v_reuseFailAlloc_2185_, 8, v_moreLinkArgs_2169_);
lean_ctor_set(v_reuseFailAlloc_2185_, 9, v_weakLinkArgs_2170_);
lean_ctor_set(v_reuseFailAlloc_2185_, 10, v_platformIndependent_2172_);
lean_ctor_set(v_reuseFailAlloc_2185_, 11, v_dynlibs_2173_);
lean_ctor_set(v_reuseFailAlloc_2185_, 12, v_plugins_2174_);
lean_ctor_set_uint8(v_reuseFailAlloc_2185_, sizeof(void*)*13, v_buildType_2160_);
lean_ctor_set_uint8(v_reuseFailAlloc_2185_, sizeof(void*)*13 + 1, v_backend_2171_);
v___x_2183_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_unbox(v___x_2181_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*13 + 2, v___x_2184_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*13 + 3, v_allowNonModules_2176_);
return v___x_2183_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3(lean_object* v_x_2187_){
_start:
{
uint8_t v___x_2188_; 
v___x_2188_ = 0;
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3___boxed(lean_object* v_x_2189_){
_start:
{
uint8_t v_res_2190_; lean_object* v_r_2191_; 
v_res_2190_ = l_Lake_LeanConfig_requiresModuleSystem___proj___lam__3(v_x_2189_);
lean_dec_ref(v_x_2189_);
v_r_2191_ = lean_box(v_res_2190_);
return v_r_2191_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_allowNonModules___proj___lam__0(lean_object* v_cfg_2203_){
_start:
{
uint8_t v_allowNonModules_2204_; 
v_allowNonModules_2204_ = lean_ctor_get_uint8(v_cfg_2203_, sizeof(void*)*13 + 3);
return v_allowNonModules_2204_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__0___boxed(lean_object* v_cfg_2205_){
_start:
{
uint8_t v_res_2206_; lean_object* v_r_2207_; 
v_res_2206_ = l_Lake_LeanConfig_allowNonModules___proj___lam__0(v_cfg_2205_);
lean_dec_ref(v_cfg_2205_);
v_r_2207_ = lean_box(v_res_2206_);
return v_r_2207_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1(uint8_t v_val_2208_, lean_object* v_cfg_2209_){
_start:
{
uint8_t v_buildType_2210_; lean_object* v_leanOptions_2211_; lean_object* v_moreLeanArgs_2212_; lean_object* v_weakLeanArgs_2213_; lean_object* v_moreLeancArgs_2214_; lean_object* v_moreServerOptions_2215_; lean_object* v_weakLeancArgs_2216_; lean_object* v_moreLinkObjs_2217_; lean_object* v_moreLinkLibs_2218_; lean_object* v_moreLinkArgs_2219_; lean_object* v_weakLinkArgs_2220_; uint8_t v_backend_2221_; lean_object* v_platformIndependent_2222_; lean_object* v_dynlibs_2223_; lean_object* v_plugins_2224_; uint8_t v_requiresModuleSystem_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
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
v_dynlibs_2223_ = lean_ctor_get(v_cfg_2209_, 11);
v_plugins_2224_ = lean_ctor_get(v_cfg_2209_, 12);
v_requiresModuleSystem_2225_ = lean_ctor_get_uint8(v_cfg_2209_, sizeof(void*)*13 + 2);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_cfg_2209_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v_cfg_2209_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_plugins_2224_);
lean_inc(v_dynlibs_2223_);
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
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_leanOptions_2211_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_moreLeanArgs_2212_);
lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_weakLeanArgs_2213_);
lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_moreLeancArgs_2214_);
lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_moreServerOptions_2215_);
lean_ctor_set(v_reuseFailAlloc_2231_, 5, v_weakLeancArgs_2216_);
lean_ctor_set(v_reuseFailAlloc_2231_, 6, v_moreLinkObjs_2217_);
lean_ctor_set(v_reuseFailAlloc_2231_, 7, v_moreLinkLibs_2218_);
lean_ctor_set(v_reuseFailAlloc_2231_, 8, v_moreLinkArgs_2219_);
lean_ctor_set(v_reuseFailAlloc_2231_, 9, v_weakLinkArgs_2220_);
lean_ctor_set(v_reuseFailAlloc_2231_, 10, v_platformIndependent_2222_);
lean_ctor_set(v_reuseFailAlloc_2231_, 11, v_dynlibs_2223_);
lean_ctor_set(v_reuseFailAlloc_2231_, 12, v_plugins_2224_);
lean_ctor_set_uint8(v_reuseFailAlloc_2231_, sizeof(void*)*13, v_buildType_2210_);
lean_ctor_set_uint8(v_reuseFailAlloc_2231_, sizeof(void*)*13 + 1, v_backend_2221_);
lean_ctor_set_uint8(v_reuseFailAlloc_2231_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_ctor_set_uint8(v___x_2230_, sizeof(void*)*13 + 3, v_val_2208_);
return v___x_2230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__1___boxed(lean_object* v_val_2233_, lean_object* v_cfg_2234_){
_start:
{
uint8_t v_val_85__boxed_2235_; lean_object* v_res_2236_; 
v_val_85__boxed_2235_ = lean_unbox(v_val_2233_);
v_res_2236_ = l_Lake_LeanConfig_allowNonModules___proj___lam__1(v_val_85__boxed_2235_, v_cfg_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_allowNonModules___proj___lam__2(lean_object* v_f_2237_, lean_object* v_cfg_2238_){
_start:
{
uint8_t v_buildType_2239_; lean_object* v_leanOptions_2240_; lean_object* v_moreLeanArgs_2241_; lean_object* v_weakLeanArgs_2242_; lean_object* v_moreLeancArgs_2243_; lean_object* v_moreServerOptions_2244_; lean_object* v_weakLeancArgs_2245_; lean_object* v_moreLinkObjs_2246_; lean_object* v_moreLinkLibs_2247_; lean_object* v_moreLinkArgs_2248_; lean_object* v_weakLinkArgs_2249_; uint8_t v_backend_2250_; lean_object* v_platformIndependent_2251_; lean_object* v_dynlibs_2252_; lean_object* v_plugins_2253_; uint8_t v_requiresModuleSystem_2254_; uint8_t v_allowNonModules_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2265_; 
v_buildType_2239_ = lean_ctor_get_uint8(v_cfg_2238_, sizeof(void*)*13);
v_leanOptions_2240_ = lean_ctor_get(v_cfg_2238_, 0);
v_moreLeanArgs_2241_ = lean_ctor_get(v_cfg_2238_, 1);
v_weakLeanArgs_2242_ = lean_ctor_get(v_cfg_2238_, 2);
v_moreLeancArgs_2243_ = lean_ctor_get(v_cfg_2238_, 3);
v_moreServerOptions_2244_ = lean_ctor_get(v_cfg_2238_, 4);
v_weakLeancArgs_2245_ = lean_ctor_get(v_cfg_2238_, 5);
v_moreLinkObjs_2246_ = lean_ctor_get(v_cfg_2238_, 6);
v_moreLinkLibs_2247_ = lean_ctor_get(v_cfg_2238_, 7);
v_moreLinkArgs_2248_ = lean_ctor_get(v_cfg_2238_, 8);
v_weakLinkArgs_2249_ = lean_ctor_get(v_cfg_2238_, 9);
v_backend_2250_ = lean_ctor_get_uint8(v_cfg_2238_, sizeof(void*)*13 + 1);
v_platformIndependent_2251_ = lean_ctor_get(v_cfg_2238_, 10);
v_dynlibs_2252_ = lean_ctor_get(v_cfg_2238_, 11);
v_plugins_2253_ = lean_ctor_get(v_cfg_2238_, 12);
v_requiresModuleSystem_2254_ = lean_ctor_get_uint8(v_cfg_2238_, sizeof(void*)*13 + 2);
v_allowNonModules_2255_ = lean_ctor_get_uint8(v_cfg_2238_, sizeof(void*)*13 + 3);
v_isSharedCheck_2265_ = !lean_is_exclusive(v_cfg_2238_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2257_ = v_cfg_2238_;
v_isShared_2258_ = v_isSharedCheck_2265_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_plugins_2253_);
lean_inc(v_dynlibs_2252_);
lean_inc(v_platformIndependent_2251_);
lean_inc(v_weakLinkArgs_2249_);
lean_inc(v_moreLinkArgs_2248_);
lean_inc(v_moreLinkLibs_2247_);
lean_inc(v_moreLinkObjs_2246_);
lean_inc(v_weakLeancArgs_2245_);
lean_inc(v_moreServerOptions_2244_);
lean_inc(v_moreLeancArgs_2243_);
lean_inc(v_weakLeanArgs_2242_);
lean_inc(v_moreLeanArgs_2241_);
lean_inc(v_leanOptions_2240_);
lean_dec(v_cfg_2238_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2265_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2259_ = lean_box(v_allowNonModules_2255_);
v___x_2260_ = lean_apply_1(v_f_2237_, v___x_2259_);
if (v_isShared_2258_ == 0)
{
v___x_2262_ = v___x_2257_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 13, 4);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_leanOptions_2240_);
lean_ctor_set(v_reuseFailAlloc_2264_, 1, v_moreLeanArgs_2241_);
lean_ctor_set(v_reuseFailAlloc_2264_, 2, v_weakLeanArgs_2242_);
lean_ctor_set(v_reuseFailAlloc_2264_, 3, v_moreLeancArgs_2243_);
lean_ctor_set(v_reuseFailAlloc_2264_, 4, v_moreServerOptions_2244_);
lean_ctor_set(v_reuseFailAlloc_2264_, 5, v_weakLeancArgs_2245_);
lean_ctor_set(v_reuseFailAlloc_2264_, 6, v_moreLinkObjs_2246_);
lean_ctor_set(v_reuseFailAlloc_2264_, 7, v_moreLinkLibs_2247_);
lean_ctor_set(v_reuseFailAlloc_2264_, 8, v_moreLinkArgs_2248_);
lean_ctor_set(v_reuseFailAlloc_2264_, 9, v_weakLinkArgs_2249_);
lean_ctor_set(v_reuseFailAlloc_2264_, 10, v_platformIndependent_2251_);
lean_ctor_set(v_reuseFailAlloc_2264_, 11, v_dynlibs_2252_);
lean_ctor_set(v_reuseFailAlloc_2264_, 12, v_plugins_2253_);
lean_ctor_set_uint8(v_reuseFailAlloc_2264_, sizeof(void*)*13, v_buildType_2239_);
lean_ctor_set_uint8(v_reuseFailAlloc_2264_, sizeof(void*)*13 + 1, v_backend_2250_);
lean_ctor_set_uint8(v_reuseFailAlloc_2264_, sizeof(void*)*13 + 2, v_requiresModuleSystem_2254_);
v___x_2262_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_unbox(v___x_2260_);
lean_ctor_set_uint8(v___x_2262_, sizeof(void*)*13 + 3, v___x_2263_);
return v___x_2262_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2285_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2286_ = lean_array_push(v___x_2285_, v___x_2284_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2293_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2294_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2295_ = lean_array_push(v___x_2294_, v___x_2293_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2303_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2304_ = lean_array_push(v___x_2303_, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2312_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2313_ = lean_array_push(v___x_2312_, v___x_2311_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2320_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2321_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2322_ = lean_array_push(v___x_2321_, v___x_2320_);
return v___x_2322_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2329_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2330_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2331_ = lean_array_push(v___x_2330_, v___x_2329_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2338_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2339_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2340_ = lean_array_push(v___x_2339_, v___x_2338_);
return v___x_2340_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2347_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2348_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2349_ = lean_array_push(v___x_2348_, v___x_2347_);
return v___x_2349_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2357_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2358_ = lean_array_push(v___x_2357_, v___x_2356_);
return v___x_2358_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2366_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2367_ = lean_array_push(v___x_2366_, v___x_2365_);
return v___x_2367_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2375_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2376_ = lean_array_push(v___x_2375_, v___x_2374_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2383_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2384_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2385_ = lean_array_push(v___x_2384_, v___x_2383_);
return v___x_2385_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2393_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2394_ = lean_array_push(v___x_2393_, v___x_2392_);
return v___x_2394_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2402_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2403_ = lean_array_push(v___x_2402_, v___x_2401_);
return v___x_2403_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2410_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2411_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2412_ = lean_array_push(v___x_2411_, v___x_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__48(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2419_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__47));
v___x_2420_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
v___x_2421_ = lean_array_push(v___x_2420_, v___x_2419_);
return v___x_2421_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__51(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___x_2428_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__50));
v___x_2429_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__48, &l_Lake_LeanConfig___fields___closed__48_once, _init_l_Lake_LeanConfig___fields___closed__48);
v___x_2430_ = lean_array_push(v___x_2429_, v___x_2428_);
return v___x_2430_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__51, &l_Lake_LeanConfig___fields___closed__51_once, _init_l_Lake_LeanConfig___fields___closed__51);
return v___x_2431_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lake_LeanConfig___fields;
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2433_, lean_object* v_x2_2434_){
_start:
{
lean_object* v_name_2435_; lean_object* v___x_2436_; 
v_name_2435_ = lean_ctor_get(v_x2_2434_, 0);
lean_inc(v_name_2435_);
v___x_2436_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2435_, v_x2_2434_, v_x1_2433_);
return v___x_2436_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = l_Lake_LeanConfig___fields;
v___x_2438_ = lean_array_get_size(v___x_2437_);
return v___x_2438_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; uint8_t v___x_2460_; 
v___x_2458_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2459_ = lean_unsigned_to_nat(0u);
v___x_2460_ = lean_nat_dec_lt(v___x_2459_, v___x_2458_);
return v___x_2460_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2461_ = lean_unsigned_to_nat(0u);
v___x_2462_ = lean_box(1);
v___x_2463_ = l_Lake_LeanConfig___fields;
v___x_2464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2464_, 0, v___x_2463_);
lean_ctor_set(v___x_2464_, 1, v___x_2462_);
lean_ctor_set(v___x_2464_, 2, v___x_2461_);
return v___x_2464_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2467_ = lean_nat_dec_le(v___x_2466_, v___x_2466_);
return v___x_2467_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2468_; size_t v___x_2469_; 
v___x_2468_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2469_ = lean_usize_of_nat(v___x_2468_);
return v___x_2469_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2470_; size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2470_ = lean_box(1);
v___x_2471_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2472_ = ((size_t)0ULL);
v___x_2473_ = l_Lake_LeanConfig___fields;
v___f_2474_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2475_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2475_, v___f_2474_, v___x_2473_, v___x_2472_, v___x_2471_, v___x_2470_);
return v___x_2476_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2479_ = l_Lake_LeanConfig___fields;
v___x_2480_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2478_);
lean_ctor_set(v___x_2480_, 2, v___x_2477_);
return v___x_2480_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
v___x_2482_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2482_;
}
else
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2483_ == 0)
{
if (v___x_2481_ == 0)
{
lean_object* v___x_2484_; 
v___x_2484_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2485_;
}
}
else
{
lean_object* v___x_2486_; 
v___x_2486_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2486_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_LeanConfig(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

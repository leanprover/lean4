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
static const lean_string_object l_Lake_instReprLeanConfig_repr___redArg___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__42 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__43;
static lean_once_cell_t l_Lake_instReprLeanConfig_repr___redArg___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__44;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__0_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__45 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__45_value;
static const lean_ctor_object l_Lake_instReprLeanConfig_repr___redArg___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__42_value)}};
static const lean_object* l_Lake_instReprLeanConfig_repr___redArg___closed__46 = (const lean_object*)&l_Lake_instReprLeanConfig_repr___redArg___closed__46_value;
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
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
lean_object* v___x_529_; 
v___x_529_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__1));
return v___x_529_;
}
else
{
lean_object* v_val_530_; lean_object* v___x_531_; uint8_t v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_val_530_ = lean_ctor_get(v_x_527_, 0);
v___x_531_ = ((lean_object*)(l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___closed__3));
v___x_532_ = lean_unbox(v_val_530_);
v___x_533_ = l_Bool_repr___redArg(v___x_532_);
v___x_534_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_531_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = l_Repr_addAppParen(v___x_534_, v_x_528_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4___boxed(lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_x_536_, v_x_537_);
lean_dec(v_x_537_);
lean_dec(v_x_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lake_instReprLeanConfig_repr_spec__5(lean_object* v_a_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = lean_nat_to_int(v_a_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(lean_object* v___y_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = l_String_quote(v___y_541_);
v___x_543_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(lean_object* v_x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
lean_dec(v_x_544_);
return v_x_545_;
}
else
{
lean_object* v_head_547_; lean_object* v_tail_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_559_; 
v_head_547_ = lean_ctor_get(v_x_546_, 0);
v_tail_548_ = lean_ctor_get(v_x_546_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_546_);
if (v_isSharedCheck_559_ == 0)
{
v___x_550_ = v_x_546_;
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_tail_548_);
lean_inc(v_head_547_);
lean_dec(v_x_546_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_559_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
lean_inc(v_x_544_);
if (v_isShared_551_ == 0)
{
lean_ctor_set_tag(v___x_550_, 5);
lean_ctor_set(v___x_550_, 1, v_x_544_);
lean_ctor_set(v___x_550_, 0, v_x_545_);
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_x_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_x_544_);
v___x_553_ = v_reuseFailAlloc_558_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = l_String_quote(v_head_547_);
v___x_555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_553_);
lean_ctor_set(v___x_556_, 1, v___x_555_);
v_x_545_ = v___x_556_;
v_x_546_ = v_tail_548_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_dec(v_x_560_);
return v_x_561_;
}
else
{
lean_object* v_head_563_; lean_object* v_tail_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_575_; 
v_head_563_ = lean_ctor_get(v_x_562_, 0);
v_tail_564_ = lean_ctor_get(v_x_562_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_575_ == 0)
{
v___x_566_ = v_x_562_;
v_isShared_567_ = v_isSharedCheck_575_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_tail_564_);
lean_inc(v_head_563_);
lean_dec(v_x_562_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_575_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
lean_inc(v_x_560_);
if (v_isShared_567_ == 0)
{
lean_ctor_set_tag(v___x_566_, 5);
lean_ctor_set(v___x_566_, 1, v_x_560_);
lean_ctor_set(v___x_566_, 0, v_x_561_);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_x_561_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_x_560_);
v___x_569_ = v_reuseFailAlloc_574_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_570_ = l_String_quote(v_head_563_);
v___x_571_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
v___x_572_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_569_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6_spec__10(v_x_560_, v___x_572_, v_tail_564_);
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_576_) == 0)
{
lean_object* v___x_578_; 
lean_dec(v_x_577_);
v___x_578_ = lean_box(0);
return v___x_578_;
}
else
{
lean_object* v_tail_579_; 
v_tail_579_ = lean_ctor_get(v_x_576_, 1);
if (lean_obj_tag(v_tail_579_) == 0)
{
lean_object* v_head_580_; lean_object* v___x_581_; 
lean_dec(v_x_577_);
v_head_580_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_head_580_);
lean_dec_ref(v_x_576_);
v___x_581_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_580_);
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
lean_inc(v_tail_579_);
v_head_582_ = lean_ctor_get(v_x_576_, 0);
lean_inc(v_head_582_);
lean_dec_ref(v_x_576_);
v___x_583_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2___lam__0(v_head_582_);
v___x_584_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2_spec__6(v_x_577_, v___x_583_, v_tail_579_);
return v___x_584_;
}
}
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__0));
v___x_594_ = lean_string_length(v___x_593_);
return v___x_594_;
}
}
static lean_object* _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6(void){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__5);
v___x_596_ = lean_nat_to_int(v___x_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(lean_object* v_xs_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_array_get_size(v_xs_604_);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_nat_dec_eq(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_608_ = lean_array_to_list(v_xs_604_);
v___x_609_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_610_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1_spec__2(v___x_608_, v___x_609_);
v___x_611_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_612_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_613_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___x_610_);
v___x_614_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_615_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_611_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Std_Format_fill(v___x_616_);
return v___x_617_;
}
else
{
lean_object* v___x_618_; 
lean_dec_ref(v_xs_604_);
v___x_618_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(lean_object* v___y_619_){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = l_Lake_Target_repr___redArg(v___y_619_, v___x_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_dec(v_x_622_);
return v_x_623_;
}
else
{
lean_object* v_head_625_; lean_object* v_tail_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_637_; 
v_head_625_ = lean_ctor_get(v_x_624_, 0);
v_tail_626_ = lean_ctor_get(v_x_624_, 1);
v_isSharedCheck_637_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_637_ == 0)
{
v___x_628_ = v_x_624_;
v_isShared_629_ = v_isSharedCheck_637_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_tail_626_);
lean_inc(v_head_625_);
lean_dec(v_x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_637_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
lean_inc(v_x_622_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 5);
lean_ctor_set(v___x_628_, 1, v_x_622_);
lean_ctor_set(v___x_628_, 0, v_x_623_);
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_x_623_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_x_622_);
v___x_631_ = v_reuseFailAlloc_636_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = l_Lake_Target_repr___redArg(v_head_625_, v___x_632_);
v___x_634_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_631_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v_x_623_ = v___x_634_;
v_x_624_ = v_tail_626_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(lean_object* v_x_638_, lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
if (lean_obj_tag(v_x_640_) == 0)
{
lean_dec(v_x_638_);
return v_x_639_;
}
else
{
lean_object* v_head_641_; lean_object* v_tail_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_653_; 
v_head_641_ = lean_ctor_get(v_x_640_, 0);
v_tail_642_ = lean_ctor_get(v_x_640_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_x_640_);
if (v_isSharedCheck_653_ == 0)
{
v___x_644_ = v_x_640_;
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_tail_642_);
lean_inc(v_head_641_);
lean_dec(v_x_640_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_653_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
lean_inc(v_x_638_);
if (v_isShared_645_ == 0)
{
lean_ctor_set_tag(v___x_644_, 5);
lean_ctor_set(v___x_644_, 1, v_x_638_);
lean_ctor_set(v___x_644_, 0, v_x_639_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_x_639_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_x_638_);
v___x_647_ = v_reuseFailAlloc_652_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Lake_Target_repr___redArg(v_head_641_, v___x_648_);
v___x_650_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_647_);
lean_ctor_set(v___x_650_, 1, v___x_649_);
v___x_651_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12_spec__16(v_x_638_, v___x_650_, v_tail_642_);
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
if (lean_obj_tag(v_x_654_) == 0)
{
lean_object* v___x_656_; 
lean_dec(v_x_655_);
v___x_656_ = lean_box(0);
return v___x_656_;
}
else
{
lean_object* v_tail_657_; 
v_tail_657_ = lean_ctor_get(v_x_654_, 1);
if (lean_obj_tag(v_tail_657_) == 0)
{
lean_object* v_head_658_; lean_object* v___x_659_; 
lean_dec(v_x_655_);
v_head_658_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_head_658_);
lean_dec_ref(v_x_654_);
v___x_659_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_658_);
return v___x_659_;
}
else
{
lean_object* v_head_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_inc(v_tail_657_);
v_head_660_ = lean_ctor_get(v_x_654_, 0);
lean_inc(v_head_660_);
lean_dec_ref(v_x_654_);
v___x_661_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_660_);
v___x_662_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6_spec__12(v_x_655_, v___x_661_, v_tail_657_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(lean_object* v_xs_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_array_get_size(v_xs_663_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_nat_dec_eq(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_667_ = lean_array_to_list(v_xs_663_);
v___x_668_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_669_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3_spec__6(v___x_667_, v___x_668_);
v___x_670_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_671_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_672_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_669_);
v___x_673_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_674_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_670_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Std_Format_fill(v___x_675_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; 
lean_dec_ref(v_xs_663_);
v___x_677_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_680_) == 0)
{
lean_dec(v_x_678_);
return v_x_679_;
}
else
{
lean_object* v_head_681_; lean_object* v_tail_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_692_; 
v_head_681_ = lean_ctor_get(v_x_680_, 0);
v_tail_682_ = lean_ctor_get(v_x_680_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_x_680_);
if (v_isSharedCheck_692_ == 0)
{
v___x_684_ = v_x_680_;
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_tail_682_);
lean_inc(v_head_681_);
lean_dec(v_x_680_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_692_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
lean_inc(v_x_678_);
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 5);
lean_ctor_set(v___x_684_, 1, v_x_678_);
lean_ctor_set(v___x_684_, 0, v_x_679_);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_x_679_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_x_678_);
v___x_687_ = v_reuseFailAlloc_691_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = l_Lean_instReprLeanOption_repr___redArg(v_head_681_);
v___x_689_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_687_);
lean_ctor_set(v___x_689_, 1, v___x_688_);
v_x_679_ = v___x_689_;
v_x_680_ = v_tail_682_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
if (lean_obj_tag(v_x_695_) == 0)
{
lean_dec(v_x_693_);
return v_x_694_;
}
else
{
lean_object* v_head_696_; lean_object* v_tail_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_707_; 
v_head_696_ = lean_ctor_get(v_x_695_, 0);
v_tail_697_ = lean_ctor_get(v_x_695_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_x_695_);
if (v_isSharedCheck_707_ == 0)
{
v___x_699_ = v_x_695_;
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_tail_697_);
lean_inc(v_head_696_);
lean_dec(v_x_695_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_707_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
lean_inc(v_x_693_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 5);
lean_ctor_set(v___x_699_, 1, v_x_693_);
lean_ctor_set(v___x_699_, 0, v_x_694_);
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_x_694_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_x_693_);
v___x_702_ = v_reuseFailAlloc_706_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = l_Lean_instReprLeanOption_repr___redArg(v_head_696_);
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3_spec__7(v_x_693_, v___x_704_, v_tail_697_);
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(lean_object* v_x_708_, lean_object* v_x_709_){
_start:
{
if (lean_obj_tag(v_x_708_) == 0)
{
lean_object* v___x_710_; 
lean_dec(v_x_709_);
v___x_710_ = lean_box(0);
return v___x_710_;
}
else
{
lean_object* v_tail_711_; 
v_tail_711_ = lean_ctor_get(v_x_708_, 1);
if (lean_obj_tag(v_tail_711_) == 0)
{
lean_object* v_head_712_; lean_object* v___x_713_; 
lean_dec(v_x_709_);
v_head_712_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_head_712_);
lean_dec_ref(v_x_708_);
v___x_713_ = l_Lean_instReprLeanOption_repr___redArg(v_head_712_);
return v___x_713_;
}
else
{
lean_object* v_head_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc(v_tail_711_);
v_head_714_ = lean_ctor_get(v_x_708_, 0);
lean_inc(v_head_714_);
lean_dec_ref(v_x_708_);
v___x_715_ = l_Lean_instReprLeanOption_repr___redArg(v_head_714_);
v___x_716_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0_spec__3(v_x_709_, v___x_715_, v_tail_711_);
return v___x_716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(lean_object* v_xs_717_){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_array_get_size(v_xs_717_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_nat_dec_eq(v___x_718_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_721_ = lean_array_to_list(v_xs_717_);
v___x_722_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_723_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0_spec__0(v___x_721_, v___x_722_);
v___x_724_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_725_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v___x_723_);
v___x_727_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_728_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_726_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_724_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Std_Format_fill(v___x_729_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; 
lean_dec_ref(v_xs_717_);
v___x_731_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_731_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
if (lean_obj_tag(v_x_734_) == 0)
{
lean_dec(v_x_732_);
return v_x_733_;
}
else
{
lean_object* v_head_735_; lean_object* v_tail_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_747_; 
v_head_735_ = lean_ctor_get(v_x_734_, 0);
v_tail_736_ = lean_ctor_get(v_x_734_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_x_734_);
if (v_isSharedCheck_747_ == 0)
{
v___x_738_ = v_x_734_;
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_tail_736_);
lean_inc(v_head_735_);
lean_dec(v_x_734_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_747_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
lean_inc(v_x_732_);
if (v_isShared_739_ == 0)
{
lean_ctor_set_tag(v___x_738_, 5);
lean_ctor_set(v___x_738_, 1, v_x_732_);
lean_ctor_set(v___x_738_, 0, v_x_733_);
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_x_733_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_x_732_);
v___x_741_ = v_reuseFailAlloc_746_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = l_Lake_Target_repr___redArg(v_head_735_, v___x_742_);
v___x_744_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v_x_733_ = v___x_744_;
v_x_734_ = v_tail_736_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
lean_dec(v_x_748_);
return v_x_749_;
}
else
{
lean_object* v_head_751_; lean_object* v_tail_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_763_; 
v_head_751_ = lean_ctor_get(v_x_750_, 0);
v_tail_752_ = lean_ctor_get(v_x_750_, 1);
v_isSharedCheck_763_ = !lean_is_exclusive(v_x_750_);
if (v_isSharedCheck_763_ == 0)
{
v___x_754_ = v_x_750_;
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_tail_752_);
lean_inc(v_head_751_);
lean_dec(v_x_750_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
lean_inc(v_x_748_);
if (v_isShared_755_ == 0)
{
lean_ctor_set_tag(v___x_754_, 5);
lean_ctor_set(v___x_754_, 1, v_x_748_);
lean_ctor_set(v___x_754_, 0, v_x_749_);
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_x_749_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_x_748_);
v___x_757_ = v_reuseFailAlloc_762_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_758_ = lean_unsigned_to_nat(0u);
v___x_759_ = l_Lake_Target_repr___redArg(v_head_751_, v___x_758_);
v___x_760_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9_spec__13(v_x_748_, v___x_760_, v_tail_752_);
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
if (lean_obj_tag(v_x_764_) == 0)
{
lean_object* v___x_766_; 
lean_dec(v_x_765_);
v___x_766_ = lean_box(0);
return v___x_766_;
}
else
{
lean_object* v_tail_767_; 
v_tail_767_ = lean_ctor_get(v_x_764_, 1);
if (lean_obj_tag(v_tail_767_) == 0)
{
lean_object* v_head_768_; lean_object* v___x_769_; 
lean_dec(v_x_765_);
v_head_768_ = lean_ctor_get(v_x_764_, 0);
lean_inc(v_head_768_);
lean_dec_ref(v_x_764_);
v___x_769_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_768_);
return v___x_769_;
}
else
{
lean_object* v_head_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_inc(v_tail_767_);
v_head_770_ = lean_ctor_get(v_x_764_, 0);
lean_inc(v_head_770_);
lean_dec_ref(v_x_764_);
v___x_771_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4___lam__0(v_head_770_);
v___x_772_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4_spec__9(v_x_765_, v___x_771_, v_tail_767_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(lean_object* v_xs_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_array_get_size(v_xs_773_);
v___x_775_ = lean_unsigned_to_nat(0u);
v___x_776_ = lean_nat_dec_eq(v___x_774_, v___x_775_);
if (v___x_776_ == 0)
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_777_ = lean_array_to_list(v_xs_773_);
v___x_778_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__3));
v___x_779_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2_spec__4(v___x_777_, v___x_778_);
v___x_780_ = lean_obj_once(&l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6, &l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6_once, _init_l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__6);
v___x_781_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__7));
v___x_782_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v___x_779_);
v___x_783_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__8));
v___x_784_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_780_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Std_Format_fill(v___x_785_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; 
lean_dec_ref(v_xs_773_);
v___x_787_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__10));
return v___x_787_;
}
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_unsigned_to_nat(13u);
v___x_802_ = lean_nat_to_int(v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_unsigned_to_nat(15u);
v___x_807_ = lean_nat_to_int(v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_unsigned_to_nat(16u);
v___x_812_ = lean_nat_to_int(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(17u);
v___x_820_ = lean_nat_to_int(v___x_819_);
return v___x_820_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(21u);
v___x_825_ = lean_nat_to_int(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_unsigned_to_nat(11u);
v___x_845_ = lean_nat_to_int(v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_unsigned_to_nat(23u);
v___x_850_ = lean_nat_to_int(v___x_849_);
return v___x_850_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__43(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__0));
v___x_859_ = lean_string_length(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__43, &l_Lake_instReprLeanConfig_repr___redArg___closed__43_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__43);
v___x_861_ = lean_nat_to_int(v___x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___redArg(lean_object* v_x_866_){
_start:
{
uint8_t v_buildType_867_; lean_object* v_leanOptions_868_; lean_object* v_moreLeanArgs_869_; lean_object* v_weakLeanArgs_870_; lean_object* v_moreLeancArgs_871_; lean_object* v_moreServerOptions_872_; lean_object* v_weakLeancArgs_873_; lean_object* v_moreLinkObjs_874_; lean_object* v_moreLinkLibs_875_; lean_object* v_moreLinkArgs_876_; lean_object* v_weakLinkArgs_877_; uint8_t v_backend_878_; lean_object* v_platformIndependent_879_; lean_object* v_dynlibs_880_; lean_object* v_plugins_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_buildType_867_ = lean_ctor_get_uint8(v_x_866_, sizeof(void*)*13);
v_leanOptions_868_ = lean_ctor_get(v_x_866_, 0);
lean_inc_ref(v_leanOptions_868_);
v_moreLeanArgs_869_ = lean_ctor_get(v_x_866_, 1);
lean_inc_ref(v_moreLeanArgs_869_);
v_weakLeanArgs_870_ = lean_ctor_get(v_x_866_, 2);
lean_inc_ref(v_weakLeanArgs_870_);
v_moreLeancArgs_871_ = lean_ctor_get(v_x_866_, 3);
lean_inc_ref(v_moreLeancArgs_871_);
v_moreServerOptions_872_ = lean_ctor_get(v_x_866_, 4);
lean_inc_ref(v_moreServerOptions_872_);
v_weakLeancArgs_873_ = lean_ctor_get(v_x_866_, 5);
lean_inc_ref(v_weakLeancArgs_873_);
v_moreLinkObjs_874_ = lean_ctor_get(v_x_866_, 6);
lean_inc_ref(v_moreLinkObjs_874_);
v_moreLinkLibs_875_ = lean_ctor_get(v_x_866_, 7);
lean_inc_ref(v_moreLinkLibs_875_);
v_moreLinkArgs_876_ = lean_ctor_get(v_x_866_, 8);
lean_inc_ref(v_moreLinkArgs_876_);
v_weakLinkArgs_877_ = lean_ctor_get(v_x_866_, 9);
lean_inc_ref(v_weakLinkArgs_877_);
v_backend_878_ = lean_ctor_get_uint8(v_x_866_, sizeof(void*)*13 + 1);
v_platformIndependent_879_ = lean_ctor_get(v_x_866_, 10);
lean_inc(v_platformIndependent_879_);
v_dynlibs_880_ = lean_ctor_get(v_x_866_, 11);
lean_inc_ref(v_dynlibs_880_);
v_plugins_881_ = lean_ctor_get(v_x_866_, 12);
lean_inc_ref(v_plugins_881_);
lean_dec_ref(v_x_866_);
v___x_882_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__5));
v___x_883_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__6));
v___x_884_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__7, &l_Lake_instReprLeanConfig_repr___redArg___closed__7_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__7);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = l_Lake_instReprBuildType_repr(v_buildType_867_, v___x_885_);
v___x_887_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_884_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = 0;
v___x_889_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set_uint8(v___x_889_, sizeof(void*)*1, v___x_888_);
v___x_890_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_883_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = ((lean_object*)(l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1___closed__2));
v___x_892_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = lean_box(1);
v___x_894_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__9));
v___x_896_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_894_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_882_);
v___x_898_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__10, &l_Lake_instReprLeanConfig_repr___redArg___closed__10_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__10);
v___x_899_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_leanOptions_868_);
v___x_900_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set_uint8(v___x_901_, sizeof(void*)*1, v___x_888_);
v___x_902_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_897_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_902_);
lean_ctor_set(v___x_903_, 1, v___x_891_);
v___x_904_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_893_);
v___x_905_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__12));
v___x_906_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v___x_882_);
v___x_908_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__13, &l_Lake_instReprLeanConfig_repr___redArg___closed__13_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__13);
v___x_909_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeanArgs_869_);
v___x_910_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set_uint8(v___x_911_, sizeof(void*)*1, v___x_888_);
v___x_912_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_907_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_891_);
v___x_914_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_893_);
v___x_915_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__15));
v___x_916_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_914_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v___x_882_);
v___x_918_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeanArgs_870_);
v___x_919_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_908_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_920_, 0, v___x_919_);
lean_ctor_set_uint8(v___x_920_, sizeof(void*)*1, v___x_888_);
v___x_921_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_917_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v___x_891_);
v___x_923_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_893_);
v___x_924_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__17));
v___x_925_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_882_);
v___x_927_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__18, &l_Lake_instReprLeanConfig_repr___redArg___closed__18_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__18);
v___x_928_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLeancArgs_871_);
v___x_929_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_930_, 0, v___x_929_);
lean_ctor_set_uint8(v___x_930_, sizeof(void*)*1, v___x_888_);
v___x_931_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_926_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v___x_891_);
v___x_933_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_893_);
v___x_934_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__20));
v___x_935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___x_882_);
v___x_937_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__21, &l_Lake_instReprLeanConfig_repr___redArg___closed__21_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__21);
v___x_938_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__0(v_moreServerOptions_872_);
v___x_939_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_940_, 0, v___x_939_);
lean_ctor_set_uint8(v___x_940_, sizeof(void*)*1, v___x_888_);
v___x_941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_936_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_891_);
v___x_943_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_893_);
v___x_944_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__23));
v___x_945_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_943_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_882_);
v___x_947_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLeancArgs_873_);
v___x_948_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_927_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_949_, 0, v___x_948_);
lean_ctor_set_uint8(v___x_949_, sizeof(void*)*1, v___x_888_);
v___x_950_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_946_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_891_);
v___x_952_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___x_893_);
v___x_953_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__25));
v___x_954_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_954_);
lean_ctor_set(v___x_955_, 1, v___x_882_);
v___x_956_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__2(v_moreLinkObjs_874_);
v___x_957_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_908_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*1, v___x_888_);
v___x_959_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_955_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_891_);
v___x_961_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_893_);
v___x_962_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__27));
v___x_963_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_882_);
v___x_965_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_moreLinkLibs_875_);
v___x_966_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_908_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set_uint8(v___x_967_, sizeof(void*)*1, v___x_888_);
v___x_968_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_964_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_891_);
v___x_970_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_893_);
v___x_971_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__29));
v___x_972_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
lean_ctor_set(v___x_972_, 1, v___x_971_);
v___x_973_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_882_);
v___x_974_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_moreLinkArgs_876_);
v___x_975_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_975_, 0, v___x_908_);
lean_ctor_set(v___x_975_, 1, v___x_974_);
v___x_976_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*1, v___x_888_);
v___x_977_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_973_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
lean_ctor_set(v___x_978_, 1, v___x_891_);
v___x_979_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v___x_893_);
v___x_980_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__31));
v___x_981_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_882_);
v___x_983_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__1(v_weakLinkArgs_877_);
v___x_984_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_908_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*1, v___x_888_);
v___x_986_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_982_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_891_);
v___x_988_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_893_);
v___x_989_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__33));
v___x_990_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_882_);
v___x_992_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__34, &l_Lake_instReprLeanConfig_repr___redArg___closed__34_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__34);
v___x_993_ = l_Lake_instReprBackend_repr(v_backend_878_, v___x_885_);
v___x_994_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
v___x_995_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*1, v___x_888_);
v___x_996_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_991_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_996_);
lean_ctor_set(v___x_997_, 1, v___x_891_);
v___x_998_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_997_);
lean_ctor_set(v___x_998_, 1, v___x_893_);
v___x_999_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__36));
v___x_1000_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v___x_882_);
v___x_1002_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__37, &l_Lake_instReprLeanConfig_repr___redArg___closed__37_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__37);
v___x_1003_ = l_Option_repr___at___00Lake_instReprLeanConfig_repr_spec__4(v_platformIndependent_879_, v___x_885_);
lean_dec(v_platformIndependent_879_);
v___x_1004_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set_uint8(v___x_1005_, sizeof(void*)*1, v___x_888_);
v___x_1006_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1001_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
lean_ctor_set(v___x_1007_, 1, v___x_891_);
v___x_1008_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v___x_893_);
v___x_1009_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__39));
v___x_1010_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
lean_ctor_set(v___x_1011_, 1, v___x_882_);
v___x_1012_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_dynlibs_880_);
v___x_1013_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_992_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1014_, 0, v___x_1013_);
lean_ctor_set_uint8(v___x_1014_, sizeof(void*)*1, v___x_888_);
v___x_1015_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1011_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_891_);
v___x_1017_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v___x_893_);
v___x_1018_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__41));
v___x_1019_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_882_);
v___x_1021_ = l_Array_repr___at___00Lake_instReprLeanConfig_repr_spec__3(v_plugins_881_);
v___x_1022_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_992_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set_uint8(v___x_1023_, sizeof(void*)*1, v___x_888_);
v___x_1024_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1020_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lake_instReprLeanConfig_repr___redArg___closed__44, &l_Lake_instReprLeanConfig_repr___redArg___closed__44_once, _init_l_Lake_instReprLeanConfig_repr___redArg___closed__44);
v___x_1026_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__45));
v___x_1027_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
lean_ctor_set(v___x_1027_, 1, v___x_1024_);
v___x_1028_ = ((lean_object*)(l_Lake_instReprLeanConfig_repr___redArg___closed__46));
v___x_1029_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1025_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set_uint8(v___x_1031_, sizeof(void*)*1, v___x_888_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr(lean_object* v_x_1032_, lean_object* v_prec_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lake_instReprLeanConfig_repr___redArg(v_x_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprLeanConfig_repr___boxed(lean_object* v_x_1035_, lean_object* v_prec_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lake_instReprLeanConfig_repr(v_x_1035_, v_prec_1036_);
lean_dec(v_prec_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__0(lean_object* v_cfg_1040_){
_start:
{
uint8_t v_buildType_1041_; 
v_buildType_1041_ = lean_ctor_get_uint8(v_cfg_1040_, sizeof(void*)*13);
return v_buildType_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__0___boxed(lean_object* v_cfg_1042_){
_start:
{
uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_res_1043_ = l_Lake_LeanConfig_buildType___proj___lam__0(v_cfg_1042_);
lean_dec_ref(v_cfg_1042_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1(uint8_t v_val_1045_, lean_object* v_cfg_1046_){
_start:
{
lean_object* v_leanOptions_1047_; lean_object* v_moreLeanArgs_1048_; lean_object* v_weakLeanArgs_1049_; lean_object* v_moreLeancArgs_1050_; lean_object* v_moreServerOptions_1051_; lean_object* v_weakLeancArgs_1052_; lean_object* v_moreLinkObjs_1053_; lean_object* v_moreLinkLibs_1054_; lean_object* v_moreLinkArgs_1055_; lean_object* v_weakLinkArgs_1056_; uint8_t v_backend_1057_; lean_object* v_platformIndependent_1058_; lean_object* v_dynlibs_1059_; lean_object* v_plugins_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
v_leanOptions_1047_ = lean_ctor_get(v_cfg_1046_, 0);
v_moreLeanArgs_1048_ = lean_ctor_get(v_cfg_1046_, 1);
v_weakLeanArgs_1049_ = lean_ctor_get(v_cfg_1046_, 2);
v_moreLeancArgs_1050_ = lean_ctor_get(v_cfg_1046_, 3);
v_moreServerOptions_1051_ = lean_ctor_get(v_cfg_1046_, 4);
v_weakLeancArgs_1052_ = lean_ctor_get(v_cfg_1046_, 5);
v_moreLinkObjs_1053_ = lean_ctor_get(v_cfg_1046_, 6);
v_moreLinkLibs_1054_ = lean_ctor_get(v_cfg_1046_, 7);
v_moreLinkArgs_1055_ = lean_ctor_get(v_cfg_1046_, 8);
v_weakLinkArgs_1056_ = lean_ctor_get(v_cfg_1046_, 9);
v_backend_1057_ = lean_ctor_get_uint8(v_cfg_1046_, sizeof(void*)*13 + 1);
v_platformIndependent_1058_ = lean_ctor_get(v_cfg_1046_, 10);
v_dynlibs_1059_ = lean_ctor_get(v_cfg_1046_, 11);
v_plugins_1060_ = lean_ctor_get(v_cfg_1046_, 12);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_cfg_1046_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v_cfg_1046_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_plugins_1060_);
lean_inc(v_dynlibs_1059_);
lean_inc(v_platformIndependent_1058_);
lean_inc(v_weakLinkArgs_1056_);
lean_inc(v_moreLinkArgs_1055_);
lean_inc(v_moreLinkLibs_1054_);
lean_inc(v_moreLinkObjs_1053_);
lean_inc(v_weakLeancArgs_1052_);
lean_inc(v_moreServerOptions_1051_);
lean_inc(v_moreLeancArgs_1050_);
lean_inc(v_weakLeanArgs_1049_);
lean_inc(v_moreLeanArgs_1048_);
lean_inc(v_leanOptions_1047_);
lean_dec(v_cfg_1046_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_leanOptions_1047_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_moreLeanArgs_1048_);
lean_ctor_set(v_reuseFailAlloc_1066_, 2, v_weakLeanArgs_1049_);
lean_ctor_set(v_reuseFailAlloc_1066_, 3, v_moreLeancArgs_1050_);
lean_ctor_set(v_reuseFailAlloc_1066_, 4, v_moreServerOptions_1051_);
lean_ctor_set(v_reuseFailAlloc_1066_, 5, v_weakLeancArgs_1052_);
lean_ctor_set(v_reuseFailAlloc_1066_, 6, v_moreLinkObjs_1053_);
lean_ctor_set(v_reuseFailAlloc_1066_, 7, v_moreLinkLibs_1054_);
lean_ctor_set(v_reuseFailAlloc_1066_, 8, v_moreLinkArgs_1055_);
lean_ctor_set(v_reuseFailAlloc_1066_, 9, v_weakLinkArgs_1056_);
lean_ctor_set(v_reuseFailAlloc_1066_, 10, v_platformIndependent_1058_);
lean_ctor_set(v_reuseFailAlloc_1066_, 11, v_dynlibs_1059_);
lean_ctor_set(v_reuseFailAlloc_1066_, 12, v_plugins_1060_);
lean_ctor_set_uint8(v_reuseFailAlloc_1066_, sizeof(void*)*13 + 1, v_backend_1057_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
lean_ctor_set_uint8(v___x_1065_, sizeof(void*)*13, v_val_1045_);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__1___boxed(lean_object* v_val_1068_, lean_object* v_cfg_1069_){
_start:
{
uint8_t v_val_79__boxed_1070_; lean_object* v_res_1071_; 
v_val_79__boxed_1070_ = lean_unbox(v_val_1068_);
v_res_1071_ = l_Lake_LeanConfig_buildType___proj___lam__1(v_val_79__boxed_1070_, v_cfg_1069_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__2(lean_object* v_f_1072_, lean_object* v_cfg_1073_){
_start:
{
uint8_t v_buildType_1074_; lean_object* v_leanOptions_1075_; lean_object* v_moreLeanArgs_1076_; lean_object* v_weakLeanArgs_1077_; lean_object* v_moreLeancArgs_1078_; lean_object* v_moreServerOptions_1079_; lean_object* v_weakLeancArgs_1080_; lean_object* v_moreLinkObjs_1081_; lean_object* v_moreLinkLibs_1082_; lean_object* v_moreLinkArgs_1083_; lean_object* v_weakLinkArgs_1084_; uint8_t v_backend_1085_; lean_object* v_platformIndependent_1086_; lean_object* v_dynlibs_1087_; lean_object* v_plugins_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1098_; 
v_buildType_1074_ = lean_ctor_get_uint8(v_cfg_1073_, sizeof(void*)*13);
v_leanOptions_1075_ = lean_ctor_get(v_cfg_1073_, 0);
v_moreLeanArgs_1076_ = lean_ctor_get(v_cfg_1073_, 1);
v_weakLeanArgs_1077_ = lean_ctor_get(v_cfg_1073_, 2);
v_moreLeancArgs_1078_ = lean_ctor_get(v_cfg_1073_, 3);
v_moreServerOptions_1079_ = lean_ctor_get(v_cfg_1073_, 4);
v_weakLeancArgs_1080_ = lean_ctor_get(v_cfg_1073_, 5);
v_moreLinkObjs_1081_ = lean_ctor_get(v_cfg_1073_, 6);
v_moreLinkLibs_1082_ = lean_ctor_get(v_cfg_1073_, 7);
v_moreLinkArgs_1083_ = lean_ctor_get(v_cfg_1073_, 8);
v_weakLinkArgs_1084_ = lean_ctor_get(v_cfg_1073_, 9);
v_backend_1085_ = lean_ctor_get_uint8(v_cfg_1073_, sizeof(void*)*13 + 1);
v_platformIndependent_1086_ = lean_ctor_get(v_cfg_1073_, 10);
v_dynlibs_1087_ = lean_ctor_get(v_cfg_1073_, 11);
v_plugins_1088_ = lean_ctor_get(v_cfg_1073_, 12);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_cfg_1073_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1090_ = v_cfg_1073_;
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_plugins_1088_);
lean_inc(v_dynlibs_1087_);
lean_inc(v_platformIndependent_1086_);
lean_inc(v_weakLinkArgs_1084_);
lean_inc(v_moreLinkArgs_1083_);
lean_inc(v_moreLinkLibs_1082_);
lean_inc(v_moreLinkObjs_1081_);
lean_inc(v_weakLeancArgs_1080_);
lean_inc(v_moreServerOptions_1079_);
lean_inc(v_moreLeancArgs_1078_);
lean_inc(v_weakLeanArgs_1077_);
lean_inc(v_moreLeanArgs_1076_);
lean_inc(v_leanOptions_1075_);
lean_dec(v_cfg_1073_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1098_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1092_ = lean_box(v_buildType_1074_);
v___x_1093_ = lean_apply_1(v_f_1072_, v___x_1092_);
if (v_isShared_1091_ == 0)
{
v___x_1095_ = v___x_1090_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_leanOptions_1075_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_moreLeanArgs_1076_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_weakLeanArgs_1077_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_moreLeancArgs_1078_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_moreServerOptions_1079_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v_weakLeancArgs_1080_);
lean_ctor_set(v_reuseFailAlloc_1097_, 6, v_moreLinkObjs_1081_);
lean_ctor_set(v_reuseFailAlloc_1097_, 7, v_moreLinkLibs_1082_);
lean_ctor_set(v_reuseFailAlloc_1097_, 8, v_moreLinkArgs_1083_);
lean_ctor_set(v_reuseFailAlloc_1097_, 9, v_weakLinkArgs_1084_);
lean_ctor_set(v_reuseFailAlloc_1097_, 10, v_platformIndependent_1086_);
lean_ctor_set(v_reuseFailAlloc_1097_, 11, v_dynlibs_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 12, v_plugins_1088_);
v___x_1095_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_unbox(v___x_1093_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*13, v___x_1096_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*13 + 1, v_backend_1085_);
return v___x_1095_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_buildType___proj___lam__3(lean_object* v_x_1099_){
_start:
{
uint8_t v___x_1100_; 
v___x_1100_ = 3;
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_buildType___proj___lam__3___boxed(lean_object* v_x_1101_){
_start:
{
uint8_t v_res_1102_; lean_object* v_r_1103_; 
v_res_1102_ = l_Lake_LeanConfig_buildType___proj___lam__3(v_x_1101_);
lean_dec_ref(v_x_1101_);
v_r_1103_ = lean_box(v_res_1102_);
return v_r_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0(lean_object* v_cfg_1115_){
_start:
{
lean_object* v_leanOptions_1116_; 
v_leanOptions_1116_ = lean_ctor_get(v_cfg_1115_, 0);
lean_inc_ref(v_leanOptions_1116_);
return v_leanOptions_1116_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__0___boxed(lean_object* v_cfg_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lake_LeanConfig_leanOptions___proj___lam__0(v_cfg_1117_);
lean_dec_ref(v_cfg_1117_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__1(lean_object* v_val_1119_, lean_object* v_cfg_1120_){
_start:
{
uint8_t v_buildType_1121_; lean_object* v_moreLeanArgs_1122_; lean_object* v_weakLeanArgs_1123_; lean_object* v_moreLeancArgs_1124_; lean_object* v_moreServerOptions_1125_; lean_object* v_weakLeancArgs_1126_; lean_object* v_moreLinkObjs_1127_; lean_object* v_moreLinkLibs_1128_; lean_object* v_moreLinkArgs_1129_; lean_object* v_weakLinkArgs_1130_; uint8_t v_backend_1131_; lean_object* v_platformIndependent_1132_; lean_object* v_dynlibs_1133_; lean_object* v_plugins_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
v_buildType_1121_ = lean_ctor_get_uint8(v_cfg_1120_, sizeof(void*)*13);
v_moreLeanArgs_1122_ = lean_ctor_get(v_cfg_1120_, 1);
v_weakLeanArgs_1123_ = lean_ctor_get(v_cfg_1120_, 2);
v_moreLeancArgs_1124_ = lean_ctor_get(v_cfg_1120_, 3);
v_moreServerOptions_1125_ = lean_ctor_get(v_cfg_1120_, 4);
v_weakLeancArgs_1126_ = lean_ctor_get(v_cfg_1120_, 5);
v_moreLinkObjs_1127_ = lean_ctor_get(v_cfg_1120_, 6);
v_moreLinkLibs_1128_ = lean_ctor_get(v_cfg_1120_, 7);
v_moreLinkArgs_1129_ = lean_ctor_get(v_cfg_1120_, 8);
v_weakLinkArgs_1130_ = lean_ctor_get(v_cfg_1120_, 9);
v_backend_1131_ = lean_ctor_get_uint8(v_cfg_1120_, sizeof(void*)*13 + 1);
v_platformIndependent_1132_ = lean_ctor_get(v_cfg_1120_, 10);
v_dynlibs_1133_ = lean_ctor_get(v_cfg_1120_, 11);
v_plugins_1134_ = lean_ctor_get(v_cfg_1120_, 12);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_cfg_1120_);
if (v_isSharedCheck_1141_ == 0)
{
lean_object* v_unused_1142_; 
v_unused_1142_ = lean_ctor_get(v_cfg_1120_, 0);
lean_dec(v_unused_1142_);
v___x_1136_ = v_cfg_1120_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_plugins_1134_);
lean_inc(v_dynlibs_1133_);
lean_inc(v_platformIndependent_1132_);
lean_inc(v_weakLinkArgs_1130_);
lean_inc(v_moreLinkArgs_1129_);
lean_inc(v_moreLinkLibs_1128_);
lean_inc(v_moreLinkObjs_1127_);
lean_inc(v_weakLeancArgs_1126_);
lean_inc(v_moreServerOptions_1125_);
lean_inc(v_moreLeancArgs_1124_);
lean_inc(v_weakLeanArgs_1123_);
lean_inc(v_moreLeanArgs_1122_);
lean_dec(v_cfg_1120_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v_val_1119_);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_val_1119_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_moreLeanArgs_1122_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_weakLeanArgs_1123_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_moreLeancArgs_1124_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_moreServerOptions_1125_);
lean_ctor_set(v_reuseFailAlloc_1140_, 5, v_weakLeancArgs_1126_);
lean_ctor_set(v_reuseFailAlloc_1140_, 6, v_moreLinkObjs_1127_);
lean_ctor_set(v_reuseFailAlloc_1140_, 7, v_moreLinkLibs_1128_);
lean_ctor_set(v_reuseFailAlloc_1140_, 8, v_moreLinkArgs_1129_);
lean_ctor_set(v_reuseFailAlloc_1140_, 9, v_weakLinkArgs_1130_);
lean_ctor_set(v_reuseFailAlloc_1140_, 10, v_platformIndependent_1132_);
lean_ctor_set(v_reuseFailAlloc_1140_, 11, v_dynlibs_1133_);
lean_ctor_set(v_reuseFailAlloc_1140_, 12, v_plugins_1134_);
lean_ctor_set_uint8(v_reuseFailAlloc_1140_, sizeof(void*)*13, v_buildType_1121_);
lean_ctor_set_uint8(v_reuseFailAlloc_1140_, sizeof(void*)*13 + 1, v_backend_1131_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__2(lean_object* v_f_1143_, lean_object* v_cfg_1144_){
_start:
{
uint8_t v_buildType_1145_; lean_object* v_leanOptions_1146_; lean_object* v_moreLeanArgs_1147_; lean_object* v_weakLeanArgs_1148_; lean_object* v_moreLeancArgs_1149_; lean_object* v_moreServerOptions_1150_; lean_object* v_weakLeancArgs_1151_; lean_object* v_moreLinkObjs_1152_; lean_object* v_moreLinkLibs_1153_; lean_object* v_moreLinkArgs_1154_; lean_object* v_weakLinkArgs_1155_; uint8_t v_backend_1156_; lean_object* v_platformIndependent_1157_; lean_object* v_dynlibs_1158_; lean_object* v_plugins_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1167_; 
v_buildType_1145_ = lean_ctor_get_uint8(v_cfg_1144_, sizeof(void*)*13);
v_leanOptions_1146_ = lean_ctor_get(v_cfg_1144_, 0);
v_moreLeanArgs_1147_ = lean_ctor_get(v_cfg_1144_, 1);
v_weakLeanArgs_1148_ = lean_ctor_get(v_cfg_1144_, 2);
v_moreLeancArgs_1149_ = lean_ctor_get(v_cfg_1144_, 3);
v_moreServerOptions_1150_ = lean_ctor_get(v_cfg_1144_, 4);
v_weakLeancArgs_1151_ = lean_ctor_get(v_cfg_1144_, 5);
v_moreLinkObjs_1152_ = lean_ctor_get(v_cfg_1144_, 6);
v_moreLinkLibs_1153_ = lean_ctor_get(v_cfg_1144_, 7);
v_moreLinkArgs_1154_ = lean_ctor_get(v_cfg_1144_, 8);
v_weakLinkArgs_1155_ = lean_ctor_get(v_cfg_1144_, 9);
v_backend_1156_ = lean_ctor_get_uint8(v_cfg_1144_, sizeof(void*)*13 + 1);
v_platformIndependent_1157_ = lean_ctor_get(v_cfg_1144_, 10);
v_dynlibs_1158_ = lean_ctor_get(v_cfg_1144_, 11);
v_plugins_1159_ = lean_ctor_get(v_cfg_1144_, 12);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_cfg_1144_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1161_ = v_cfg_1144_;
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_plugins_1159_);
lean_inc(v_dynlibs_1158_);
lean_inc(v_platformIndependent_1157_);
lean_inc(v_weakLinkArgs_1155_);
lean_inc(v_moreLinkArgs_1154_);
lean_inc(v_moreLinkLibs_1153_);
lean_inc(v_moreLinkObjs_1152_);
lean_inc(v_weakLeancArgs_1151_);
lean_inc(v_moreServerOptions_1150_);
lean_inc(v_moreLeancArgs_1149_);
lean_inc(v_weakLeanArgs_1148_);
lean_inc(v_moreLeanArgs_1147_);
lean_inc(v_leanOptions_1146_);
lean_dec(v_cfg_1144_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1167_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = lean_apply_1(v_f_1143_, v_leanOptions_1146_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1163_);
v___x_1165_ = v___x_1161_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_moreLeanArgs_1147_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_weakLeanArgs_1148_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_moreLeancArgs_1149_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_moreServerOptions_1150_);
lean_ctor_set(v_reuseFailAlloc_1166_, 5, v_weakLeancArgs_1151_);
lean_ctor_set(v_reuseFailAlloc_1166_, 6, v_moreLinkObjs_1152_);
lean_ctor_set(v_reuseFailAlloc_1166_, 7, v_moreLinkLibs_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 8, v_moreLinkArgs_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 9, v_weakLinkArgs_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 10, v_platformIndependent_1157_);
lean_ctor_set(v_reuseFailAlloc_1166_, 11, v_dynlibs_1158_);
lean_ctor_set(v_reuseFailAlloc_1166_, 12, v_plugins_1159_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*13, v_buildType_1145_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*13 + 1, v_backend_1156_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3(lean_object* v_x_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = ((lean_object*)(l_Lake_instInhabitedLeanConfig_default___closed__0));
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_leanOptions___proj___lam__3___boxed(lean_object* v_x_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Lake_LeanConfig_leanOptions___proj___lam__3(v_x_1170_);
lean_dec_ref(v_x_1170_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(lean_object* v_cfg_1183_){
_start:
{
lean_object* v_moreLeanArgs_1184_; 
v_moreLeanArgs_1184_ = lean_ctor_get(v_cfg_1183_, 1);
lean_inc_ref(v_moreLeanArgs_1184_);
return v_moreLeanArgs_1184_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__0(v_cfg_1185_);
lean_dec_ref(v_cfg_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__1(lean_object* v_val_1187_, lean_object* v_cfg_1188_){
_start:
{
uint8_t v_buildType_1189_; lean_object* v_leanOptions_1190_; lean_object* v_weakLeanArgs_1191_; lean_object* v_moreLeancArgs_1192_; lean_object* v_moreServerOptions_1193_; lean_object* v_weakLeancArgs_1194_; lean_object* v_moreLinkObjs_1195_; lean_object* v_moreLinkLibs_1196_; lean_object* v_moreLinkArgs_1197_; lean_object* v_weakLinkArgs_1198_; uint8_t v_backend_1199_; lean_object* v_platformIndependent_1200_; lean_object* v_dynlibs_1201_; lean_object* v_plugins_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
v_buildType_1189_ = lean_ctor_get_uint8(v_cfg_1188_, sizeof(void*)*13);
v_leanOptions_1190_ = lean_ctor_get(v_cfg_1188_, 0);
v_weakLeanArgs_1191_ = lean_ctor_get(v_cfg_1188_, 2);
v_moreLeancArgs_1192_ = lean_ctor_get(v_cfg_1188_, 3);
v_moreServerOptions_1193_ = lean_ctor_get(v_cfg_1188_, 4);
v_weakLeancArgs_1194_ = lean_ctor_get(v_cfg_1188_, 5);
v_moreLinkObjs_1195_ = lean_ctor_get(v_cfg_1188_, 6);
v_moreLinkLibs_1196_ = lean_ctor_get(v_cfg_1188_, 7);
v_moreLinkArgs_1197_ = lean_ctor_get(v_cfg_1188_, 8);
v_weakLinkArgs_1198_ = lean_ctor_get(v_cfg_1188_, 9);
v_backend_1199_ = lean_ctor_get_uint8(v_cfg_1188_, sizeof(void*)*13 + 1);
v_platformIndependent_1200_ = lean_ctor_get(v_cfg_1188_, 10);
v_dynlibs_1201_ = lean_ctor_get(v_cfg_1188_, 11);
v_plugins_1202_ = lean_ctor_get(v_cfg_1188_, 12);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_cfg_1188_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_cfg_1188_, 1);
lean_dec(v_unused_1210_);
v___x_1204_ = v_cfg_1188_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_plugins_1202_);
lean_inc(v_dynlibs_1201_);
lean_inc(v_platformIndependent_1200_);
lean_inc(v_weakLinkArgs_1198_);
lean_inc(v_moreLinkArgs_1197_);
lean_inc(v_moreLinkLibs_1196_);
lean_inc(v_moreLinkObjs_1195_);
lean_inc(v_weakLeancArgs_1194_);
lean_inc(v_moreServerOptions_1193_);
lean_inc(v_moreLeancArgs_1192_);
lean_inc(v_weakLeanArgs_1191_);
lean_inc(v_leanOptions_1190_);
lean_dec(v_cfg_1188_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_val_1187_);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_leanOptions_1190_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_val_1187_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_weakLeanArgs_1191_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_moreLeancArgs_1192_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_moreServerOptions_1193_);
lean_ctor_set(v_reuseFailAlloc_1208_, 5, v_weakLeancArgs_1194_);
lean_ctor_set(v_reuseFailAlloc_1208_, 6, v_moreLinkObjs_1195_);
lean_ctor_set(v_reuseFailAlloc_1208_, 7, v_moreLinkLibs_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 8, v_moreLinkArgs_1197_);
lean_ctor_set(v_reuseFailAlloc_1208_, 9, v_weakLinkArgs_1198_);
lean_ctor_set(v_reuseFailAlloc_1208_, 10, v_platformIndependent_1200_);
lean_ctor_set(v_reuseFailAlloc_1208_, 11, v_dynlibs_1201_);
lean_ctor_set(v_reuseFailAlloc_1208_, 12, v_plugins_1202_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*13, v_buildType_1189_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*13 + 1, v_backend_1199_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__2(lean_object* v_f_1211_, lean_object* v_cfg_1212_){
_start:
{
uint8_t v_buildType_1213_; lean_object* v_leanOptions_1214_; lean_object* v_moreLeanArgs_1215_; lean_object* v_weakLeanArgs_1216_; lean_object* v_moreLeancArgs_1217_; lean_object* v_moreServerOptions_1218_; lean_object* v_weakLeancArgs_1219_; lean_object* v_moreLinkObjs_1220_; lean_object* v_moreLinkLibs_1221_; lean_object* v_moreLinkArgs_1222_; lean_object* v_weakLinkArgs_1223_; uint8_t v_backend_1224_; lean_object* v_platformIndependent_1225_; lean_object* v_dynlibs_1226_; lean_object* v_plugins_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1235_; 
v_buildType_1213_ = lean_ctor_get_uint8(v_cfg_1212_, sizeof(void*)*13);
v_leanOptions_1214_ = lean_ctor_get(v_cfg_1212_, 0);
v_moreLeanArgs_1215_ = lean_ctor_get(v_cfg_1212_, 1);
v_weakLeanArgs_1216_ = lean_ctor_get(v_cfg_1212_, 2);
v_moreLeancArgs_1217_ = lean_ctor_get(v_cfg_1212_, 3);
v_moreServerOptions_1218_ = lean_ctor_get(v_cfg_1212_, 4);
v_weakLeancArgs_1219_ = lean_ctor_get(v_cfg_1212_, 5);
v_moreLinkObjs_1220_ = lean_ctor_get(v_cfg_1212_, 6);
v_moreLinkLibs_1221_ = lean_ctor_get(v_cfg_1212_, 7);
v_moreLinkArgs_1222_ = lean_ctor_get(v_cfg_1212_, 8);
v_weakLinkArgs_1223_ = lean_ctor_get(v_cfg_1212_, 9);
v_backend_1224_ = lean_ctor_get_uint8(v_cfg_1212_, sizeof(void*)*13 + 1);
v_platformIndependent_1225_ = lean_ctor_get(v_cfg_1212_, 10);
v_dynlibs_1226_ = lean_ctor_get(v_cfg_1212_, 11);
v_plugins_1227_ = lean_ctor_get(v_cfg_1212_, 12);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_cfg_1212_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1229_ = v_cfg_1212_;
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_plugins_1227_);
lean_inc(v_dynlibs_1226_);
lean_inc(v_platformIndependent_1225_);
lean_inc(v_weakLinkArgs_1223_);
lean_inc(v_moreLinkArgs_1222_);
lean_inc(v_moreLinkLibs_1221_);
lean_inc(v_moreLinkObjs_1220_);
lean_inc(v_weakLeancArgs_1219_);
lean_inc(v_moreServerOptions_1218_);
lean_inc(v_moreLeancArgs_1217_);
lean_inc(v_weakLeanArgs_1216_);
lean_inc(v_moreLeanArgs_1215_);
lean_inc(v_leanOptions_1214_);
lean_dec(v_cfg_1212_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1235_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_apply_1(v_f_1211_, v_moreLeanArgs_1215_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1231_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_leanOptions_1214_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_weakLeanArgs_1216_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_moreLeancArgs_1217_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v_moreServerOptions_1218_);
lean_ctor_set(v_reuseFailAlloc_1234_, 5, v_weakLeancArgs_1219_);
lean_ctor_set(v_reuseFailAlloc_1234_, 6, v_moreLinkObjs_1220_);
lean_ctor_set(v_reuseFailAlloc_1234_, 7, v_moreLinkLibs_1221_);
lean_ctor_set(v_reuseFailAlloc_1234_, 8, v_moreLinkArgs_1222_);
lean_ctor_set(v_reuseFailAlloc_1234_, 9, v_weakLinkArgs_1223_);
lean_ctor_set(v_reuseFailAlloc_1234_, 10, v_platformIndependent_1225_);
lean_ctor_set(v_reuseFailAlloc_1234_, 11, v_dynlibs_1226_);
lean_ctor_set(v_reuseFailAlloc_1234_, 12, v_plugins_1227_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*13, v_buildType_1213_);
lean_ctor_set_uint8(v_reuseFailAlloc_1234_, sizeof(void*)*13 + 1, v_backend_1224_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(lean_object* v_x_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = ((lean_object*)(l_Lake_BuildType_leanArgs___closed__0));
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeanArgs___proj___lam__3___boxed(lean_object* v_x_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lake_LeanConfig_moreLeanArgs___proj___lam__3(v_x_1238_);
lean_dec_ref(v_x_1238_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(lean_object* v_cfg_1251_){
_start:
{
lean_object* v_weakLeanArgs_1252_; 
v_weakLeanArgs_1252_ = lean_ctor_get(v_cfg_1251_, 2);
lean_inc_ref(v_weakLeanArgs_1252_);
return v_weakLeanArgs_1252_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__0___boxed(lean_object* v_cfg_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lake_LeanConfig_weakLeanArgs___proj___lam__0(v_cfg_1253_);
lean_dec_ref(v_cfg_1253_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__1(lean_object* v_val_1255_, lean_object* v_cfg_1256_){
_start:
{
uint8_t v_buildType_1257_; lean_object* v_leanOptions_1258_; lean_object* v_moreLeanArgs_1259_; lean_object* v_moreLeancArgs_1260_; lean_object* v_moreServerOptions_1261_; lean_object* v_weakLeancArgs_1262_; lean_object* v_moreLinkObjs_1263_; lean_object* v_moreLinkLibs_1264_; lean_object* v_moreLinkArgs_1265_; lean_object* v_weakLinkArgs_1266_; uint8_t v_backend_1267_; lean_object* v_platformIndependent_1268_; lean_object* v_dynlibs_1269_; lean_object* v_plugins_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
v_buildType_1257_ = lean_ctor_get_uint8(v_cfg_1256_, sizeof(void*)*13);
v_leanOptions_1258_ = lean_ctor_get(v_cfg_1256_, 0);
v_moreLeanArgs_1259_ = lean_ctor_get(v_cfg_1256_, 1);
v_moreLeancArgs_1260_ = lean_ctor_get(v_cfg_1256_, 3);
v_moreServerOptions_1261_ = lean_ctor_get(v_cfg_1256_, 4);
v_weakLeancArgs_1262_ = lean_ctor_get(v_cfg_1256_, 5);
v_moreLinkObjs_1263_ = lean_ctor_get(v_cfg_1256_, 6);
v_moreLinkLibs_1264_ = lean_ctor_get(v_cfg_1256_, 7);
v_moreLinkArgs_1265_ = lean_ctor_get(v_cfg_1256_, 8);
v_weakLinkArgs_1266_ = lean_ctor_get(v_cfg_1256_, 9);
v_backend_1267_ = lean_ctor_get_uint8(v_cfg_1256_, sizeof(void*)*13 + 1);
v_platformIndependent_1268_ = lean_ctor_get(v_cfg_1256_, 10);
v_dynlibs_1269_ = lean_ctor_get(v_cfg_1256_, 11);
v_plugins_1270_ = lean_ctor_get(v_cfg_1256_, 12);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_cfg_1256_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v_cfg_1256_, 2);
lean_dec(v_unused_1278_);
v___x_1272_ = v_cfg_1256_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
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
lean_inc(v_moreLeanArgs_1259_);
lean_inc(v_leanOptions_1258_);
lean_dec(v_cfg_1256_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 2, v_val_1255_);
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_leanOptions_1258_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_moreLeanArgs_1259_);
lean_ctor_set(v_reuseFailAlloc_1276_, 2, v_val_1255_);
lean_ctor_set(v_reuseFailAlloc_1276_, 3, v_moreLeancArgs_1260_);
lean_ctor_set(v_reuseFailAlloc_1276_, 4, v_moreServerOptions_1261_);
lean_ctor_set(v_reuseFailAlloc_1276_, 5, v_weakLeancArgs_1262_);
lean_ctor_set(v_reuseFailAlloc_1276_, 6, v_moreLinkObjs_1263_);
lean_ctor_set(v_reuseFailAlloc_1276_, 7, v_moreLinkLibs_1264_);
lean_ctor_set(v_reuseFailAlloc_1276_, 8, v_moreLinkArgs_1265_);
lean_ctor_set(v_reuseFailAlloc_1276_, 9, v_weakLinkArgs_1266_);
lean_ctor_set(v_reuseFailAlloc_1276_, 10, v_platformIndependent_1268_);
lean_ctor_set(v_reuseFailAlloc_1276_, 11, v_dynlibs_1269_);
lean_ctor_set(v_reuseFailAlloc_1276_, 12, v_plugins_1270_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13, v_buildType_1257_);
lean_ctor_set_uint8(v_reuseFailAlloc_1276_, sizeof(void*)*13 + 1, v_backend_1267_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeanArgs___proj___lam__2(lean_object* v_f_1279_, lean_object* v_cfg_1280_){
_start:
{
uint8_t v_buildType_1281_; lean_object* v_leanOptions_1282_; lean_object* v_moreLeanArgs_1283_; lean_object* v_weakLeanArgs_1284_; lean_object* v_moreLeancArgs_1285_; lean_object* v_moreServerOptions_1286_; lean_object* v_weakLeancArgs_1287_; lean_object* v_moreLinkObjs_1288_; lean_object* v_moreLinkLibs_1289_; lean_object* v_moreLinkArgs_1290_; lean_object* v_weakLinkArgs_1291_; uint8_t v_backend_1292_; lean_object* v_platformIndependent_1293_; lean_object* v_dynlibs_1294_; lean_object* v_plugins_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1303_; 
v_buildType_1281_ = lean_ctor_get_uint8(v_cfg_1280_, sizeof(void*)*13);
v_leanOptions_1282_ = lean_ctor_get(v_cfg_1280_, 0);
v_moreLeanArgs_1283_ = lean_ctor_get(v_cfg_1280_, 1);
v_weakLeanArgs_1284_ = lean_ctor_get(v_cfg_1280_, 2);
v_moreLeancArgs_1285_ = lean_ctor_get(v_cfg_1280_, 3);
v_moreServerOptions_1286_ = lean_ctor_get(v_cfg_1280_, 4);
v_weakLeancArgs_1287_ = lean_ctor_get(v_cfg_1280_, 5);
v_moreLinkObjs_1288_ = lean_ctor_get(v_cfg_1280_, 6);
v_moreLinkLibs_1289_ = lean_ctor_get(v_cfg_1280_, 7);
v_moreLinkArgs_1290_ = lean_ctor_get(v_cfg_1280_, 8);
v_weakLinkArgs_1291_ = lean_ctor_get(v_cfg_1280_, 9);
v_backend_1292_ = lean_ctor_get_uint8(v_cfg_1280_, sizeof(void*)*13 + 1);
v_platformIndependent_1293_ = lean_ctor_get(v_cfg_1280_, 10);
v_dynlibs_1294_ = lean_ctor_get(v_cfg_1280_, 11);
v_plugins_1295_ = lean_ctor_get(v_cfg_1280_, 12);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_cfg_1280_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1297_ = v_cfg_1280_;
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_plugins_1295_);
lean_inc(v_dynlibs_1294_);
lean_inc(v_platformIndependent_1293_);
lean_inc(v_weakLinkArgs_1291_);
lean_inc(v_moreLinkArgs_1290_);
lean_inc(v_moreLinkLibs_1289_);
lean_inc(v_moreLinkObjs_1288_);
lean_inc(v_weakLeancArgs_1287_);
lean_inc(v_moreServerOptions_1286_);
lean_inc(v_moreLeancArgs_1285_);
lean_inc(v_weakLeanArgs_1284_);
lean_inc(v_moreLeanArgs_1283_);
lean_inc(v_leanOptions_1282_);
lean_dec(v_cfg_1280_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_apply_1(v_f_1279_, v_weakLeanArgs_1284_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 2, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_leanOptions_1282_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_moreLeanArgs_1283_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_moreLeancArgs_1285_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_moreServerOptions_1286_);
lean_ctor_set(v_reuseFailAlloc_1302_, 5, v_weakLeancArgs_1287_);
lean_ctor_set(v_reuseFailAlloc_1302_, 6, v_moreLinkObjs_1288_);
lean_ctor_set(v_reuseFailAlloc_1302_, 7, v_moreLinkLibs_1289_);
lean_ctor_set(v_reuseFailAlloc_1302_, 8, v_moreLinkArgs_1290_);
lean_ctor_set(v_reuseFailAlloc_1302_, 9, v_weakLinkArgs_1291_);
lean_ctor_set(v_reuseFailAlloc_1302_, 10, v_platformIndependent_1293_);
lean_ctor_set(v_reuseFailAlloc_1302_, 11, v_dynlibs_1294_);
lean_ctor_set(v_reuseFailAlloc_1302_, 12, v_plugins_1295_);
lean_ctor_set_uint8(v_reuseFailAlloc_1302_, sizeof(void*)*13, v_buildType_1281_);
lean_ctor_set_uint8(v_reuseFailAlloc_1302_, sizeof(void*)*13 + 1, v_backend_1292_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(lean_object* v_cfg_1314_){
_start:
{
lean_object* v_moreLeancArgs_1315_; 
v_moreLeancArgs_1315_ = lean_ctor_get(v_cfg_1314_, 3);
lean_inc_ref(v_moreLeancArgs_1315_);
return v_moreLeancArgs_1315_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lake_LeanConfig_moreLeancArgs___proj___lam__0(v_cfg_1316_);
lean_dec_ref(v_cfg_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__1(lean_object* v_val_1318_, lean_object* v_cfg_1319_){
_start:
{
uint8_t v_buildType_1320_; lean_object* v_leanOptions_1321_; lean_object* v_moreLeanArgs_1322_; lean_object* v_weakLeanArgs_1323_; lean_object* v_moreServerOptions_1324_; lean_object* v_weakLeancArgs_1325_; lean_object* v_moreLinkObjs_1326_; lean_object* v_moreLinkLibs_1327_; lean_object* v_moreLinkArgs_1328_; lean_object* v_weakLinkArgs_1329_; uint8_t v_backend_1330_; lean_object* v_platformIndependent_1331_; lean_object* v_dynlibs_1332_; lean_object* v_plugins_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_buildType_1320_ = lean_ctor_get_uint8(v_cfg_1319_, sizeof(void*)*13);
v_leanOptions_1321_ = lean_ctor_get(v_cfg_1319_, 0);
v_moreLeanArgs_1322_ = lean_ctor_get(v_cfg_1319_, 1);
v_weakLeanArgs_1323_ = lean_ctor_get(v_cfg_1319_, 2);
v_moreServerOptions_1324_ = lean_ctor_get(v_cfg_1319_, 4);
v_weakLeancArgs_1325_ = lean_ctor_get(v_cfg_1319_, 5);
v_moreLinkObjs_1326_ = lean_ctor_get(v_cfg_1319_, 6);
v_moreLinkLibs_1327_ = lean_ctor_get(v_cfg_1319_, 7);
v_moreLinkArgs_1328_ = lean_ctor_get(v_cfg_1319_, 8);
v_weakLinkArgs_1329_ = lean_ctor_get(v_cfg_1319_, 9);
v_backend_1330_ = lean_ctor_get_uint8(v_cfg_1319_, sizeof(void*)*13 + 1);
v_platformIndependent_1331_ = lean_ctor_get(v_cfg_1319_, 10);
v_dynlibs_1332_ = lean_ctor_get(v_cfg_1319_, 11);
v_plugins_1333_ = lean_ctor_get(v_cfg_1319_, 12);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_cfg_1319_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_cfg_1319_, 3);
lean_dec(v_unused_1341_);
v___x_1335_ = v_cfg_1319_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
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
lean_inc(v_weakLeanArgs_1323_);
lean_inc(v_moreLeanArgs_1322_);
lean_inc(v_leanOptions_1321_);
lean_dec(v_cfg_1319_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 3, v_val_1318_);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_leanOptions_1321_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_moreLeanArgs_1322_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_weakLeanArgs_1323_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_val_1318_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_moreServerOptions_1324_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v_weakLeancArgs_1325_);
lean_ctor_set(v_reuseFailAlloc_1339_, 6, v_moreLinkObjs_1326_);
lean_ctor_set(v_reuseFailAlloc_1339_, 7, v_moreLinkLibs_1327_);
lean_ctor_set(v_reuseFailAlloc_1339_, 8, v_moreLinkArgs_1328_);
lean_ctor_set(v_reuseFailAlloc_1339_, 9, v_weakLinkArgs_1329_);
lean_ctor_set(v_reuseFailAlloc_1339_, 10, v_platformIndependent_1331_);
lean_ctor_set(v_reuseFailAlloc_1339_, 11, v_dynlibs_1332_);
lean_ctor_set(v_reuseFailAlloc_1339_, 12, v_plugins_1333_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*13, v_buildType_1320_);
lean_ctor_set_uint8(v_reuseFailAlloc_1339_, sizeof(void*)*13 + 1, v_backend_1330_);
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
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLeancArgs___proj___lam__2(lean_object* v_f_1342_, lean_object* v_cfg_1343_){
_start:
{
uint8_t v_buildType_1344_; lean_object* v_leanOptions_1345_; lean_object* v_moreLeanArgs_1346_; lean_object* v_weakLeanArgs_1347_; lean_object* v_moreLeancArgs_1348_; lean_object* v_moreServerOptions_1349_; lean_object* v_weakLeancArgs_1350_; lean_object* v_moreLinkObjs_1351_; lean_object* v_moreLinkLibs_1352_; lean_object* v_moreLinkArgs_1353_; lean_object* v_weakLinkArgs_1354_; uint8_t v_backend_1355_; lean_object* v_platformIndependent_1356_; lean_object* v_dynlibs_1357_; lean_object* v_plugins_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1366_; 
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
v_dynlibs_1357_ = lean_ctor_get(v_cfg_1343_, 11);
v_plugins_1358_ = lean_ctor_get(v_cfg_1343_, 12);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_cfg_1343_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1360_ = v_cfg_1343_;
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_plugins_1358_);
lean_inc(v_dynlibs_1357_);
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
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1366_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1362_ = lean_apply_1(v_f_1342_, v_moreLeancArgs_1348_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 3, v___x_1362_);
v___x_1364_ = v___x_1360_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_leanOptions_1345_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_moreLeanArgs_1346_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_weakLeanArgs_1347_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_moreServerOptions_1349_);
lean_ctor_set(v_reuseFailAlloc_1365_, 5, v_weakLeancArgs_1350_);
lean_ctor_set(v_reuseFailAlloc_1365_, 6, v_moreLinkObjs_1351_);
lean_ctor_set(v_reuseFailAlloc_1365_, 7, v_moreLinkLibs_1352_);
lean_ctor_set(v_reuseFailAlloc_1365_, 8, v_moreLinkArgs_1353_);
lean_ctor_set(v_reuseFailAlloc_1365_, 9, v_weakLinkArgs_1354_);
lean_ctor_set(v_reuseFailAlloc_1365_, 10, v_platformIndependent_1356_);
lean_ctor_set(v_reuseFailAlloc_1365_, 11, v_dynlibs_1357_);
lean_ctor_set(v_reuseFailAlloc_1365_, 12, v_plugins_1358_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*13, v_buildType_1344_);
lean_ctor_set_uint8(v_reuseFailAlloc_1365_, sizeof(void*)*13 + 1, v_backend_1355_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0(lean_object* v_cfg_1377_){
_start:
{
lean_object* v_moreServerOptions_1378_; 
v_moreServerOptions_1378_ = lean_ctor_get(v_cfg_1377_, 4);
lean_inc_ref(v_moreServerOptions_1378_);
return v_moreServerOptions_1378_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__0___boxed(lean_object* v_cfg_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Lake_LeanConfig_moreServerOptions___proj___lam__0(v_cfg_1379_);
lean_dec_ref(v_cfg_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__1(lean_object* v_val_1381_, lean_object* v_cfg_1382_){
_start:
{
uint8_t v_buildType_1383_; lean_object* v_leanOptions_1384_; lean_object* v_moreLeanArgs_1385_; lean_object* v_weakLeanArgs_1386_; lean_object* v_moreLeancArgs_1387_; lean_object* v_weakLeancArgs_1388_; lean_object* v_moreLinkObjs_1389_; lean_object* v_moreLinkLibs_1390_; lean_object* v_moreLinkArgs_1391_; lean_object* v_weakLinkArgs_1392_; uint8_t v_backend_1393_; lean_object* v_platformIndependent_1394_; lean_object* v_dynlibs_1395_; lean_object* v_plugins_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1403_; 
v_buildType_1383_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*13);
v_leanOptions_1384_ = lean_ctor_get(v_cfg_1382_, 0);
v_moreLeanArgs_1385_ = lean_ctor_get(v_cfg_1382_, 1);
v_weakLeanArgs_1386_ = lean_ctor_get(v_cfg_1382_, 2);
v_moreLeancArgs_1387_ = lean_ctor_get(v_cfg_1382_, 3);
v_weakLeancArgs_1388_ = lean_ctor_get(v_cfg_1382_, 5);
v_moreLinkObjs_1389_ = lean_ctor_get(v_cfg_1382_, 6);
v_moreLinkLibs_1390_ = lean_ctor_get(v_cfg_1382_, 7);
v_moreLinkArgs_1391_ = lean_ctor_get(v_cfg_1382_, 8);
v_weakLinkArgs_1392_ = lean_ctor_get(v_cfg_1382_, 9);
v_backend_1393_ = lean_ctor_get_uint8(v_cfg_1382_, sizeof(void*)*13 + 1);
v_platformIndependent_1394_ = lean_ctor_get(v_cfg_1382_, 10);
v_dynlibs_1395_ = lean_ctor_get(v_cfg_1382_, 11);
v_plugins_1396_ = lean_ctor_get(v_cfg_1382_, 12);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_cfg_1382_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_cfg_1382_, 4);
lean_dec(v_unused_1404_);
v___x_1398_ = v_cfg_1382_;
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_plugins_1396_);
lean_inc(v_dynlibs_1395_);
lean_inc(v_platformIndependent_1394_);
lean_inc(v_weakLinkArgs_1392_);
lean_inc(v_moreLinkArgs_1391_);
lean_inc(v_moreLinkLibs_1390_);
lean_inc(v_moreLinkObjs_1389_);
lean_inc(v_weakLeancArgs_1388_);
lean_inc(v_moreLeancArgs_1387_);
lean_inc(v_weakLeanArgs_1386_);
lean_inc(v_moreLeanArgs_1385_);
lean_inc(v_leanOptions_1384_);
lean_dec(v_cfg_1382_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1403_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v_val_1381_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_leanOptions_1384_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_moreLeanArgs_1385_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_weakLeanArgs_1386_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_moreLeancArgs_1387_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_val_1381_);
lean_ctor_set(v_reuseFailAlloc_1402_, 5, v_weakLeancArgs_1388_);
lean_ctor_set(v_reuseFailAlloc_1402_, 6, v_moreLinkObjs_1389_);
lean_ctor_set(v_reuseFailAlloc_1402_, 7, v_moreLinkLibs_1390_);
lean_ctor_set(v_reuseFailAlloc_1402_, 8, v_moreLinkArgs_1391_);
lean_ctor_set(v_reuseFailAlloc_1402_, 9, v_weakLinkArgs_1392_);
lean_ctor_set(v_reuseFailAlloc_1402_, 10, v_platformIndependent_1394_);
lean_ctor_set(v_reuseFailAlloc_1402_, 11, v_dynlibs_1395_);
lean_ctor_set(v_reuseFailAlloc_1402_, 12, v_plugins_1396_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*13, v_buildType_1383_);
lean_ctor_set_uint8(v_reuseFailAlloc_1402_, sizeof(void*)*13 + 1, v_backend_1393_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreServerOptions___proj___lam__2(lean_object* v_f_1405_, lean_object* v_cfg_1406_){
_start:
{
uint8_t v_buildType_1407_; lean_object* v_leanOptions_1408_; lean_object* v_moreLeanArgs_1409_; lean_object* v_weakLeanArgs_1410_; lean_object* v_moreLeancArgs_1411_; lean_object* v_moreServerOptions_1412_; lean_object* v_weakLeancArgs_1413_; lean_object* v_moreLinkObjs_1414_; lean_object* v_moreLinkLibs_1415_; lean_object* v_moreLinkArgs_1416_; lean_object* v_weakLinkArgs_1417_; uint8_t v_backend_1418_; lean_object* v_platformIndependent_1419_; lean_object* v_dynlibs_1420_; lean_object* v_plugins_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_buildType_1407_ = lean_ctor_get_uint8(v_cfg_1406_, sizeof(void*)*13);
v_leanOptions_1408_ = lean_ctor_get(v_cfg_1406_, 0);
v_moreLeanArgs_1409_ = lean_ctor_get(v_cfg_1406_, 1);
v_weakLeanArgs_1410_ = lean_ctor_get(v_cfg_1406_, 2);
v_moreLeancArgs_1411_ = lean_ctor_get(v_cfg_1406_, 3);
v_moreServerOptions_1412_ = lean_ctor_get(v_cfg_1406_, 4);
v_weakLeancArgs_1413_ = lean_ctor_get(v_cfg_1406_, 5);
v_moreLinkObjs_1414_ = lean_ctor_get(v_cfg_1406_, 6);
v_moreLinkLibs_1415_ = lean_ctor_get(v_cfg_1406_, 7);
v_moreLinkArgs_1416_ = lean_ctor_get(v_cfg_1406_, 8);
v_weakLinkArgs_1417_ = lean_ctor_get(v_cfg_1406_, 9);
v_backend_1418_ = lean_ctor_get_uint8(v_cfg_1406_, sizeof(void*)*13 + 1);
v_platformIndependent_1419_ = lean_ctor_get(v_cfg_1406_, 10);
v_dynlibs_1420_ = lean_ctor_get(v_cfg_1406_, 11);
v_plugins_1421_ = lean_ctor_get(v_cfg_1406_, 12);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_cfg_1406_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1423_ = v_cfg_1406_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_plugins_1421_);
lean_inc(v_dynlibs_1420_);
lean_inc(v_platformIndependent_1419_);
lean_inc(v_weakLinkArgs_1417_);
lean_inc(v_moreLinkArgs_1416_);
lean_inc(v_moreLinkLibs_1415_);
lean_inc(v_moreLinkObjs_1414_);
lean_inc(v_weakLeancArgs_1413_);
lean_inc(v_moreServerOptions_1412_);
lean_inc(v_moreLeancArgs_1411_);
lean_inc(v_weakLeanArgs_1410_);
lean_inc(v_moreLeanArgs_1409_);
lean_inc(v_leanOptions_1408_);
lean_dec(v_cfg_1406_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_apply_1(v_f_1405_, v_moreServerOptions_1412_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 4, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_leanOptions_1408_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_moreLeanArgs_1409_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_weakLeanArgs_1410_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_moreLeancArgs_1411_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1428_, 5, v_weakLeancArgs_1413_);
lean_ctor_set(v_reuseFailAlloc_1428_, 6, v_moreLinkObjs_1414_);
lean_ctor_set(v_reuseFailAlloc_1428_, 7, v_moreLinkLibs_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 8, v_moreLinkArgs_1416_);
lean_ctor_set(v_reuseFailAlloc_1428_, 9, v_weakLinkArgs_1417_);
lean_ctor_set(v_reuseFailAlloc_1428_, 10, v_platformIndependent_1419_);
lean_ctor_set(v_reuseFailAlloc_1428_, 11, v_dynlibs_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 12, v_plugins_1421_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13, v_buildType_1407_);
lean_ctor_set_uint8(v_reuseFailAlloc_1428_, sizeof(void*)*13 + 1, v_backend_1418_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(lean_object* v_cfg_1440_){
_start:
{
lean_object* v_weakLeancArgs_1441_; 
v_weakLeancArgs_1441_ = lean_ctor_get(v_cfg_1440_, 5);
lean_inc_ref(v_weakLeancArgs_1441_);
return v_weakLeancArgs_1441_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__0___boxed(lean_object* v_cfg_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lake_LeanConfig_weakLeancArgs___proj___lam__0(v_cfg_1442_);
lean_dec_ref(v_cfg_1442_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__1(lean_object* v_val_1444_, lean_object* v_cfg_1445_){
_start:
{
uint8_t v_buildType_1446_; lean_object* v_leanOptions_1447_; lean_object* v_moreLeanArgs_1448_; lean_object* v_weakLeanArgs_1449_; lean_object* v_moreLeancArgs_1450_; lean_object* v_moreServerOptions_1451_; lean_object* v_moreLinkObjs_1452_; lean_object* v_moreLinkLibs_1453_; lean_object* v_moreLinkArgs_1454_; lean_object* v_weakLinkArgs_1455_; uint8_t v_backend_1456_; lean_object* v_platformIndependent_1457_; lean_object* v_dynlibs_1458_; lean_object* v_plugins_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
v_buildType_1446_ = lean_ctor_get_uint8(v_cfg_1445_, sizeof(void*)*13);
v_leanOptions_1447_ = lean_ctor_get(v_cfg_1445_, 0);
v_moreLeanArgs_1448_ = lean_ctor_get(v_cfg_1445_, 1);
v_weakLeanArgs_1449_ = lean_ctor_get(v_cfg_1445_, 2);
v_moreLeancArgs_1450_ = lean_ctor_get(v_cfg_1445_, 3);
v_moreServerOptions_1451_ = lean_ctor_get(v_cfg_1445_, 4);
v_moreLinkObjs_1452_ = lean_ctor_get(v_cfg_1445_, 6);
v_moreLinkLibs_1453_ = lean_ctor_get(v_cfg_1445_, 7);
v_moreLinkArgs_1454_ = lean_ctor_get(v_cfg_1445_, 8);
v_weakLinkArgs_1455_ = lean_ctor_get(v_cfg_1445_, 9);
v_backend_1456_ = lean_ctor_get_uint8(v_cfg_1445_, sizeof(void*)*13 + 1);
v_platformIndependent_1457_ = lean_ctor_get(v_cfg_1445_, 10);
v_dynlibs_1458_ = lean_ctor_get(v_cfg_1445_, 11);
v_plugins_1459_ = lean_ctor_get(v_cfg_1445_, 12);
v_isSharedCheck_1466_ = !lean_is_exclusive(v_cfg_1445_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v_cfg_1445_, 5);
lean_dec(v_unused_1467_);
v___x_1461_ = v_cfg_1445_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_plugins_1459_);
lean_inc(v_dynlibs_1458_);
lean_inc(v_platformIndependent_1457_);
lean_inc(v_weakLinkArgs_1455_);
lean_inc(v_moreLinkArgs_1454_);
lean_inc(v_moreLinkLibs_1453_);
lean_inc(v_moreLinkObjs_1452_);
lean_inc(v_moreServerOptions_1451_);
lean_inc(v_moreLeancArgs_1450_);
lean_inc(v_weakLeanArgs_1449_);
lean_inc(v_moreLeanArgs_1448_);
lean_inc(v_leanOptions_1447_);
lean_dec(v_cfg_1445_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 5, v_val_1444_);
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_leanOptions_1447_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_moreLeanArgs_1448_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_weakLeanArgs_1449_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_moreLeancArgs_1450_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_moreServerOptions_1451_);
lean_ctor_set(v_reuseFailAlloc_1465_, 5, v_val_1444_);
lean_ctor_set(v_reuseFailAlloc_1465_, 6, v_moreLinkObjs_1452_);
lean_ctor_set(v_reuseFailAlloc_1465_, 7, v_moreLinkLibs_1453_);
lean_ctor_set(v_reuseFailAlloc_1465_, 8, v_moreLinkArgs_1454_);
lean_ctor_set(v_reuseFailAlloc_1465_, 9, v_weakLinkArgs_1455_);
lean_ctor_set(v_reuseFailAlloc_1465_, 10, v_platformIndependent_1457_);
lean_ctor_set(v_reuseFailAlloc_1465_, 11, v_dynlibs_1458_);
lean_ctor_set(v_reuseFailAlloc_1465_, 12, v_plugins_1459_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*13, v_buildType_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1465_, sizeof(void*)*13 + 1, v_backend_1456_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLeancArgs___proj___lam__2(lean_object* v_f_1468_, lean_object* v_cfg_1469_){
_start:
{
uint8_t v_buildType_1470_; lean_object* v_leanOptions_1471_; lean_object* v_moreLeanArgs_1472_; lean_object* v_weakLeanArgs_1473_; lean_object* v_moreLeancArgs_1474_; lean_object* v_moreServerOptions_1475_; lean_object* v_weakLeancArgs_1476_; lean_object* v_moreLinkObjs_1477_; lean_object* v_moreLinkLibs_1478_; lean_object* v_moreLinkArgs_1479_; lean_object* v_weakLinkArgs_1480_; uint8_t v_backend_1481_; lean_object* v_platformIndependent_1482_; lean_object* v_dynlibs_1483_; lean_object* v_plugins_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1492_; 
v_buildType_1470_ = lean_ctor_get_uint8(v_cfg_1469_, sizeof(void*)*13);
v_leanOptions_1471_ = lean_ctor_get(v_cfg_1469_, 0);
v_moreLeanArgs_1472_ = lean_ctor_get(v_cfg_1469_, 1);
v_weakLeanArgs_1473_ = lean_ctor_get(v_cfg_1469_, 2);
v_moreLeancArgs_1474_ = lean_ctor_get(v_cfg_1469_, 3);
v_moreServerOptions_1475_ = lean_ctor_get(v_cfg_1469_, 4);
v_weakLeancArgs_1476_ = lean_ctor_get(v_cfg_1469_, 5);
v_moreLinkObjs_1477_ = lean_ctor_get(v_cfg_1469_, 6);
v_moreLinkLibs_1478_ = lean_ctor_get(v_cfg_1469_, 7);
v_moreLinkArgs_1479_ = lean_ctor_get(v_cfg_1469_, 8);
v_weakLinkArgs_1480_ = lean_ctor_get(v_cfg_1469_, 9);
v_backend_1481_ = lean_ctor_get_uint8(v_cfg_1469_, sizeof(void*)*13 + 1);
v_platformIndependent_1482_ = lean_ctor_get(v_cfg_1469_, 10);
v_dynlibs_1483_ = lean_ctor_get(v_cfg_1469_, 11);
v_plugins_1484_ = lean_ctor_get(v_cfg_1469_, 12);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_cfg_1469_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1486_ = v_cfg_1469_;
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_plugins_1484_);
lean_inc(v_dynlibs_1483_);
lean_inc(v_platformIndependent_1482_);
lean_inc(v_weakLinkArgs_1480_);
lean_inc(v_moreLinkArgs_1479_);
lean_inc(v_moreLinkLibs_1478_);
lean_inc(v_moreLinkObjs_1477_);
lean_inc(v_weakLeancArgs_1476_);
lean_inc(v_moreServerOptions_1475_);
lean_inc(v_moreLeancArgs_1474_);
lean_inc(v_weakLeanArgs_1473_);
lean_inc(v_moreLeanArgs_1472_);
lean_inc(v_leanOptions_1471_);
lean_dec(v_cfg_1469_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = lean_apply_1(v_f_1468_, v_weakLeancArgs_1476_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 5, v___x_1488_);
v___x_1490_ = v___x_1486_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_leanOptions_1471_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_moreLeanArgs_1472_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_weakLeanArgs_1473_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_moreLeancArgs_1474_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v_moreServerOptions_1475_);
lean_ctor_set(v_reuseFailAlloc_1491_, 5, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1491_, 6, v_moreLinkObjs_1477_);
lean_ctor_set(v_reuseFailAlloc_1491_, 7, v_moreLinkLibs_1478_);
lean_ctor_set(v_reuseFailAlloc_1491_, 8, v_moreLinkArgs_1479_);
lean_ctor_set(v_reuseFailAlloc_1491_, 9, v_weakLinkArgs_1480_);
lean_ctor_set(v_reuseFailAlloc_1491_, 10, v_platformIndependent_1482_);
lean_ctor_set(v_reuseFailAlloc_1491_, 11, v_dynlibs_1483_);
lean_ctor_set(v_reuseFailAlloc_1491_, 12, v_plugins_1484_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*13, v_buildType_1470_);
lean_ctor_set_uint8(v_reuseFailAlloc_1491_, sizeof(void*)*13 + 1, v_backend_1481_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(lean_object* v_cfg_1503_){
_start:
{
lean_object* v_moreLinkObjs_1504_; 
v_moreLinkObjs_1504_ = lean_ctor_get(v_cfg_1503_, 6);
lean_inc_ref(v_moreLinkObjs_1504_);
return v_moreLinkObjs_1504_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__0___boxed(lean_object* v_cfg_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__0(v_cfg_1505_);
lean_dec_ref(v_cfg_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__1(lean_object* v_val_1507_, lean_object* v_cfg_1508_){
_start:
{
uint8_t v_buildType_1509_; lean_object* v_leanOptions_1510_; lean_object* v_moreLeanArgs_1511_; lean_object* v_weakLeanArgs_1512_; lean_object* v_moreLeancArgs_1513_; lean_object* v_moreServerOptions_1514_; lean_object* v_weakLeancArgs_1515_; lean_object* v_moreLinkLibs_1516_; lean_object* v_moreLinkArgs_1517_; lean_object* v_weakLinkArgs_1518_; uint8_t v_backend_1519_; lean_object* v_platformIndependent_1520_; lean_object* v_dynlibs_1521_; lean_object* v_plugins_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_buildType_1509_ = lean_ctor_get_uint8(v_cfg_1508_, sizeof(void*)*13);
v_leanOptions_1510_ = lean_ctor_get(v_cfg_1508_, 0);
v_moreLeanArgs_1511_ = lean_ctor_get(v_cfg_1508_, 1);
v_weakLeanArgs_1512_ = lean_ctor_get(v_cfg_1508_, 2);
v_moreLeancArgs_1513_ = lean_ctor_get(v_cfg_1508_, 3);
v_moreServerOptions_1514_ = lean_ctor_get(v_cfg_1508_, 4);
v_weakLeancArgs_1515_ = lean_ctor_get(v_cfg_1508_, 5);
v_moreLinkLibs_1516_ = lean_ctor_get(v_cfg_1508_, 7);
v_moreLinkArgs_1517_ = lean_ctor_get(v_cfg_1508_, 8);
v_weakLinkArgs_1518_ = lean_ctor_get(v_cfg_1508_, 9);
v_backend_1519_ = lean_ctor_get_uint8(v_cfg_1508_, sizeof(void*)*13 + 1);
v_platformIndependent_1520_ = lean_ctor_get(v_cfg_1508_, 10);
v_dynlibs_1521_ = lean_ctor_get(v_cfg_1508_, 11);
v_plugins_1522_ = lean_ctor_get(v_cfg_1508_, 12);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_cfg_1508_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; 
v_unused_1530_ = lean_ctor_get(v_cfg_1508_, 6);
lean_dec(v_unused_1530_);
v___x_1524_ = v_cfg_1508_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_plugins_1522_);
lean_inc(v_dynlibs_1521_);
lean_inc(v_platformIndependent_1520_);
lean_inc(v_weakLinkArgs_1518_);
lean_inc(v_moreLinkArgs_1517_);
lean_inc(v_moreLinkLibs_1516_);
lean_inc(v_weakLeancArgs_1515_);
lean_inc(v_moreServerOptions_1514_);
lean_inc(v_moreLeancArgs_1513_);
lean_inc(v_weakLeanArgs_1512_);
lean_inc(v_moreLeanArgs_1511_);
lean_inc(v_leanOptions_1510_);
lean_dec(v_cfg_1508_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 6, v_val_1507_);
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_leanOptions_1510_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v_moreLeanArgs_1511_);
lean_ctor_set(v_reuseFailAlloc_1528_, 2, v_weakLeanArgs_1512_);
lean_ctor_set(v_reuseFailAlloc_1528_, 3, v_moreLeancArgs_1513_);
lean_ctor_set(v_reuseFailAlloc_1528_, 4, v_moreServerOptions_1514_);
lean_ctor_set(v_reuseFailAlloc_1528_, 5, v_weakLeancArgs_1515_);
lean_ctor_set(v_reuseFailAlloc_1528_, 6, v_val_1507_);
lean_ctor_set(v_reuseFailAlloc_1528_, 7, v_moreLinkLibs_1516_);
lean_ctor_set(v_reuseFailAlloc_1528_, 8, v_moreLinkArgs_1517_);
lean_ctor_set(v_reuseFailAlloc_1528_, 9, v_weakLinkArgs_1518_);
lean_ctor_set(v_reuseFailAlloc_1528_, 10, v_platformIndependent_1520_);
lean_ctor_set(v_reuseFailAlloc_1528_, 11, v_dynlibs_1521_);
lean_ctor_set(v_reuseFailAlloc_1528_, 12, v_plugins_1522_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13, v_buildType_1509_);
lean_ctor_set_uint8(v_reuseFailAlloc_1528_, sizeof(void*)*13 + 1, v_backend_1519_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__2(lean_object* v_f_1531_, lean_object* v_cfg_1532_){
_start:
{
uint8_t v_buildType_1533_; lean_object* v_leanOptions_1534_; lean_object* v_moreLeanArgs_1535_; lean_object* v_weakLeanArgs_1536_; lean_object* v_moreLeancArgs_1537_; lean_object* v_moreServerOptions_1538_; lean_object* v_weakLeancArgs_1539_; lean_object* v_moreLinkObjs_1540_; lean_object* v_moreLinkLibs_1541_; lean_object* v_moreLinkArgs_1542_; lean_object* v_weakLinkArgs_1543_; uint8_t v_backend_1544_; lean_object* v_platformIndependent_1545_; lean_object* v_dynlibs_1546_; lean_object* v_plugins_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_buildType_1533_ = lean_ctor_get_uint8(v_cfg_1532_, sizeof(void*)*13);
v_leanOptions_1534_ = lean_ctor_get(v_cfg_1532_, 0);
v_moreLeanArgs_1535_ = lean_ctor_get(v_cfg_1532_, 1);
v_weakLeanArgs_1536_ = lean_ctor_get(v_cfg_1532_, 2);
v_moreLeancArgs_1537_ = lean_ctor_get(v_cfg_1532_, 3);
v_moreServerOptions_1538_ = lean_ctor_get(v_cfg_1532_, 4);
v_weakLeancArgs_1539_ = lean_ctor_get(v_cfg_1532_, 5);
v_moreLinkObjs_1540_ = lean_ctor_get(v_cfg_1532_, 6);
v_moreLinkLibs_1541_ = lean_ctor_get(v_cfg_1532_, 7);
v_moreLinkArgs_1542_ = lean_ctor_get(v_cfg_1532_, 8);
v_weakLinkArgs_1543_ = lean_ctor_get(v_cfg_1532_, 9);
v_backend_1544_ = lean_ctor_get_uint8(v_cfg_1532_, sizeof(void*)*13 + 1);
v_platformIndependent_1545_ = lean_ctor_get(v_cfg_1532_, 10);
v_dynlibs_1546_ = lean_ctor_get(v_cfg_1532_, 11);
v_plugins_1547_ = lean_ctor_get(v_cfg_1532_, 12);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_cfg_1532_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1549_ = v_cfg_1532_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_plugins_1547_);
lean_inc(v_dynlibs_1546_);
lean_inc(v_platformIndependent_1545_);
lean_inc(v_weakLinkArgs_1543_);
lean_inc(v_moreLinkArgs_1542_);
lean_inc(v_moreLinkLibs_1541_);
lean_inc(v_moreLinkObjs_1540_);
lean_inc(v_weakLeancArgs_1539_);
lean_inc(v_moreServerOptions_1538_);
lean_inc(v_moreLeancArgs_1537_);
lean_inc(v_weakLeanArgs_1536_);
lean_inc(v_moreLeanArgs_1535_);
lean_inc(v_leanOptions_1534_);
lean_dec(v_cfg_1532_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_apply_1(v_f_1531_, v_moreLinkObjs_1540_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 6, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_leanOptions_1534_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_moreLeanArgs_1535_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v_weakLeanArgs_1536_);
lean_ctor_set(v_reuseFailAlloc_1554_, 3, v_moreLeancArgs_1537_);
lean_ctor_set(v_reuseFailAlloc_1554_, 4, v_moreServerOptions_1538_);
lean_ctor_set(v_reuseFailAlloc_1554_, 5, v_weakLeancArgs_1539_);
lean_ctor_set(v_reuseFailAlloc_1554_, 6, v___x_1551_);
lean_ctor_set(v_reuseFailAlloc_1554_, 7, v_moreLinkLibs_1541_);
lean_ctor_set(v_reuseFailAlloc_1554_, 8, v_moreLinkArgs_1542_);
lean_ctor_set(v_reuseFailAlloc_1554_, 9, v_weakLinkArgs_1543_);
lean_ctor_set(v_reuseFailAlloc_1554_, 10, v_platformIndependent_1545_);
lean_ctor_set(v_reuseFailAlloc_1554_, 11, v_dynlibs_1546_);
lean_ctor_set(v_reuseFailAlloc_1554_, 12, v_plugins_1547_);
lean_ctor_set_uint8(v_reuseFailAlloc_1554_, sizeof(void*)*13, v_buildType_1533_);
lean_ctor_set_uint8(v_reuseFailAlloc_1554_, sizeof(void*)*13 + 1, v_backend_1544_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(lean_object* v_x_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = ((lean_object*)(l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___closed__0));
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkObjs___proj___lam__3___boxed(lean_object* v_x_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lake_LeanConfig_moreLinkObjs___proj___lam__3(v_x_1560_);
lean_dec_ref(v_x_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(lean_object* v_cfg_1573_){
_start:
{
lean_object* v_moreLinkLibs_1574_; 
v_moreLinkLibs_1574_ = lean_ctor_get(v_cfg_1573_, 7);
lean_inc_ref(v_moreLinkLibs_1574_);
return v_moreLinkLibs_1574_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__0___boxed(lean_object* v_cfg_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lake_LeanConfig_moreLinkLibs___proj___lam__0(v_cfg_1575_);
lean_dec_ref(v_cfg_1575_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__1(lean_object* v_val_1577_, lean_object* v_cfg_1578_){
_start:
{
uint8_t v_buildType_1579_; lean_object* v_leanOptions_1580_; lean_object* v_moreLeanArgs_1581_; lean_object* v_weakLeanArgs_1582_; lean_object* v_moreLeancArgs_1583_; lean_object* v_moreServerOptions_1584_; lean_object* v_weakLeancArgs_1585_; lean_object* v_moreLinkObjs_1586_; lean_object* v_moreLinkArgs_1587_; lean_object* v_weakLinkArgs_1588_; uint8_t v_backend_1589_; lean_object* v_platformIndependent_1590_; lean_object* v_dynlibs_1591_; lean_object* v_plugins_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_buildType_1579_ = lean_ctor_get_uint8(v_cfg_1578_, sizeof(void*)*13);
v_leanOptions_1580_ = lean_ctor_get(v_cfg_1578_, 0);
v_moreLeanArgs_1581_ = lean_ctor_get(v_cfg_1578_, 1);
v_weakLeanArgs_1582_ = lean_ctor_get(v_cfg_1578_, 2);
v_moreLeancArgs_1583_ = lean_ctor_get(v_cfg_1578_, 3);
v_moreServerOptions_1584_ = lean_ctor_get(v_cfg_1578_, 4);
v_weakLeancArgs_1585_ = lean_ctor_get(v_cfg_1578_, 5);
v_moreLinkObjs_1586_ = lean_ctor_get(v_cfg_1578_, 6);
v_moreLinkArgs_1587_ = lean_ctor_get(v_cfg_1578_, 8);
v_weakLinkArgs_1588_ = lean_ctor_get(v_cfg_1578_, 9);
v_backend_1589_ = lean_ctor_get_uint8(v_cfg_1578_, sizeof(void*)*13 + 1);
v_platformIndependent_1590_ = lean_ctor_get(v_cfg_1578_, 10);
v_dynlibs_1591_ = lean_ctor_get(v_cfg_1578_, 11);
v_plugins_1592_ = lean_ctor_get(v_cfg_1578_, 12);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_cfg_1578_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v_cfg_1578_, 7);
lean_dec(v_unused_1600_);
v___x_1594_ = v_cfg_1578_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_plugins_1592_);
lean_inc(v_dynlibs_1591_);
lean_inc(v_platformIndependent_1590_);
lean_inc(v_weakLinkArgs_1588_);
lean_inc(v_moreLinkArgs_1587_);
lean_inc(v_moreLinkObjs_1586_);
lean_inc(v_weakLeancArgs_1585_);
lean_inc(v_moreServerOptions_1584_);
lean_inc(v_moreLeancArgs_1583_);
lean_inc(v_weakLeanArgs_1582_);
lean_inc(v_moreLeanArgs_1581_);
lean_inc(v_leanOptions_1580_);
lean_dec(v_cfg_1578_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 7, v_val_1577_);
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_leanOptions_1580_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_moreLeanArgs_1581_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_weakLeanArgs_1582_);
lean_ctor_set(v_reuseFailAlloc_1598_, 3, v_moreLeancArgs_1583_);
lean_ctor_set(v_reuseFailAlloc_1598_, 4, v_moreServerOptions_1584_);
lean_ctor_set(v_reuseFailAlloc_1598_, 5, v_weakLeancArgs_1585_);
lean_ctor_set(v_reuseFailAlloc_1598_, 6, v_moreLinkObjs_1586_);
lean_ctor_set(v_reuseFailAlloc_1598_, 7, v_val_1577_);
lean_ctor_set(v_reuseFailAlloc_1598_, 8, v_moreLinkArgs_1587_);
lean_ctor_set(v_reuseFailAlloc_1598_, 9, v_weakLinkArgs_1588_);
lean_ctor_set(v_reuseFailAlloc_1598_, 10, v_platformIndependent_1590_);
lean_ctor_set(v_reuseFailAlloc_1598_, 11, v_dynlibs_1591_);
lean_ctor_set(v_reuseFailAlloc_1598_, 12, v_plugins_1592_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, sizeof(void*)*13, v_buildType_1579_);
lean_ctor_set_uint8(v_reuseFailAlloc_1598_, sizeof(void*)*13 + 1, v_backend_1589_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkLibs___proj___lam__2(lean_object* v_f_1601_, lean_object* v_cfg_1602_){
_start:
{
uint8_t v_buildType_1603_; lean_object* v_leanOptions_1604_; lean_object* v_moreLeanArgs_1605_; lean_object* v_weakLeanArgs_1606_; lean_object* v_moreLeancArgs_1607_; lean_object* v_moreServerOptions_1608_; lean_object* v_weakLeancArgs_1609_; lean_object* v_moreLinkObjs_1610_; lean_object* v_moreLinkLibs_1611_; lean_object* v_moreLinkArgs_1612_; lean_object* v_weakLinkArgs_1613_; uint8_t v_backend_1614_; lean_object* v_platformIndependent_1615_; lean_object* v_dynlibs_1616_; lean_object* v_plugins_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1625_; 
v_buildType_1603_ = lean_ctor_get_uint8(v_cfg_1602_, sizeof(void*)*13);
v_leanOptions_1604_ = lean_ctor_get(v_cfg_1602_, 0);
v_moreLeanArgs_1605_ = lean_ctor_get(v_cfg_1602_, 1);
v_weakLeanArgs_1606_ = lean_ctor_get(v_cfg_1602_, 2);
v_moreLeancArgs_1607_ = lean_ctor_get(v_cfg_1602_, 3);
v_moreServerOptions_1608_ = lean_ctor_get(v_cfg_1602_, 4);
v_weakLeancArgs_1609_ = lean_ctor_get(v_cfg_1602_, 5);
v_moreLinkObjs_1610_ = lean_ctor_get(v_cfg_1602_, 6);
v_moreLinkLibs_1611_ = lean_ctor_get(v_cfg_1602_, 7);
v_moreLinkArgs_1612_ = lean_ctor_get(v_cfg_1602_, 8);
v_weakLinkArgs_1613_ = lean_ctor_get(v_cfg_1602_, 9);
v_backend_1614_ = lean_ctor_get_uint8(v_cfg_1602_, sizeof(void*)*13 + 1);
v_platformIndependent_1615_ = lean_ctor_get(v_cfg_1602_, 10);
v_dynlibs_1616_ = lean_ctor_get(v_cfg_1602_, 11);
v_plugins_1617_ = lean_ctor_get(v_cfg_1602_, 12);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_cfg_1602_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1619_ = v_cfg_1602_;
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_plugins_1617_);
lean_inc(v_dynlibs_1616_);
lean_inc(v_platformIndependent_1615_);
lean_inc(v_weakLinkArgs_1613_);
lean_inc(v_moreLinkArgs_1612_);
lean_inc(v_moreLinkLibs_1611_);
lean_inc(v_moreLinkObjs_1610_);
lean_inc(v_weakLeancArgs_1609_);
lean_inc(v_moreServerOptions_1608_);
lean_inc(v_moreLeancArgs_1607_);
lean_inc(v_weakLeanArgs_1606_);
lean_inc(v_moreLeanArgs_1605_);
lean_inc(v_leanOptions_1604_);
lean_dec(v_cfg_1602_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_apply_1(v_f_1601_, v_moreLinkLibs_1611_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 7, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_leanOptions_1604_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_moreLeanArgs_1605_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v_weakLeanArgs_1606_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v_moreLeancArgs_1607_);
lean_ctor_set(v_reuseFailAlloc_1624_, 4, v_moreServerOptions_1608_);
lean_ctor_set(v_reuseFailAlloc_1624_, 5, v_weakLeancArgs_1609_);
lean_ctor_set(v_reuseFailAlloc_1624_, 6, v_moreLinkObjs_1610_);
lean_ctor_set(v_reuseFailAlloc_1624_, 7, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1624_, 8, v_moreLinkArgs_1612_);
lean_ctor_set(v_reuseFailAlloc_1624_, 9, v_weakLinkArgs_1613_);
lean_ctor_set(v_reuseFailAlloc_1624_, 10, v_platformIndependent_1615_);
lean_ctor_set(v_reuseFailAlloc_1624_, 11, v_dynlibs_1616_);
lean_ctor_set(v_reuseFailAlloc_1624_, 12, v_plugins_1617_);
lean_ctor_set_uint8(v_reuseFailAlloc_1624_, sizeof(void*)*13, v_buildType_1603_);
lean_ctor_set_uint8(v_reuseFailAlloc_1624_, sizeof(void*)*13 + 1, v_backend_1614_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(lean_object* v_cfg_1636_){
_start:
{
lean_object* v_moreLinkArgs_1637_; 
v_moreLinkArgs_1637_ = lean_ctor_get(v_cfg_1636_, 8);
lean_inc_ref(v_moreLinkArgs_1637_);
return v_moreLinkArgs_1637_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lake_LeanConfig_moreLinkArgs___proj___lam__0(v_cfg_1638_);
lean_dec_ref(v_cfg_1638_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__1(lean_object* v_val_1640_, lean_object* v_cfg_1641_){
_start:
{
uint8_t v_buildType_1642_; lean_object* v_leanOptions_1643_; lean_object* v_moreLeanArgs_1644_; lean_object* v_weakLeanArgs_1645_; lean_object* v_moreLeancArgs_1646_; lean_object* v_moreServerOptions_1647_; lean_object* v_weakLeancArgs_1648_; lean_object* v_moreLinkObjs_1649_; lean_object* v_moreLinkLibs_1650_; lean_object* v_weakLinkArgs_1651_; uint8_t v_backend_1652_; lean_object* v_platformIndependent_1653_; lean_object* v_dynlibs_1654_; lean_object* v_plugins_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
v_buildType_1642_ = lean_ctor_get_uint8(v_cfg_1641_, sizeof(void*)*13);
v_leanOptions_1643_ = lean_ctor_get(v_cfg_1641_, 0);
v_moreLeanArgs_1644_ = lean_ctor_get(v_cfg_1641_, 1);
v_weakLeanArgs_1645_ = lean_ctor_get(v_cfg_1641_, 2);
v_moreLeancArgs_1646_ = lean_ctor_get(v_cfg_1641_, 3);
v_moreServerOptions_1647_ = lean_ctor_get(v_cfg_1641_, 4);
v_weakLeancArgs_1648_ = lean_ctor_get(v_cfg_1641_, 5);
v_moreLinkObjs_1649_ = lean_ctor_get(v_cfg_1641_, 6);
v_moreLinkLibs_1650_ = lean_ctor_get(v_cfg_1641_, 7);
v_weakLinkArgs_1651_ = lean_ctor_get(v_cfg_1641_, 9);
v_backend_1652_ = lean_ctor_get_uint8(v_cfg_1641_, sizeof(void*)*13 + 1);
v_platformIndependent_1653_ = lean_ctor_get(v_cfg_1641_, 10);
v_dynlibs_1654_ = lean_ctor_get(v_cfg_1641_, 11);
v_plugins_1655_ = lean_ctor_get(v_cfg_1641_, 12);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_cfg_1641_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v_cfg_1641_, 8);
lean_dec(v_unused_1663_);
v___x_1657_ = v_cfg_1641_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_plugins_1655_);
lean_inc(v_dynlibs_1654_);
lean_inc(v_platformIndependent_1653_);
lean_inc(v_weakLinkArgs_1651_);
lean_inc(v_moreLinkLibs_1650_);
lean_inc(v_moreLinkObjs_1649_);
lean_inc(v_weakLeancArgs_1648_);
lean_inc(v_moreServerOptions_1647_);
lean_inc(v_moreLeancArgs_1646_);
lean_inc(v_weakLeanArgs_1645_);
lean_inc(v_moreLeanArgs_1644_);
lean_inc(v_leanOptions_1643_);
lean_dec(v_cfg_1641_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 8, v_val_1640_);
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_leanOptions_1643_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_moreLeanArgs_1644_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_weakLeanArgs_1645_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_moreLeancArgs_1646_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_moreServerOptions_1647_);
lean_ctor_set(v_reuseFailAlloc_1661_, 5, v_weakLeancArgs_1648_);
lean_ctor_set(v_reuseFailAlloc_1661_, 6, v_moreLinkObjs_1649_);
lean_ctor_set(v_reuseFailAlloc_1661_, 7, v_moreLinkLibs_1650_);
lean_ctor_set(v_reuseFailAlloc_1661_, 8, v_val_1640_);
lean_ctor_set(v_reuseFailAlloc_1661_, 9, v_weakLinkArgs_1651_);
lean_ctor_set(v_reuseFailAlloc_1661_, 10, v_platformIndependent_1653_);
lean_ctor_set(v_reuseFailAlloc_1661_, 11, v_dynlibs_1654_);
lean_ctor_set(v_reuseFailAlloc_1661_, 12, v_plugins_1655_);
lean_ctor_set_uint8(v_reuseFailAlloc_1661_, sizeof(void*)*13, v_buildType_1642_);
lean_ctor_set_uint8(v_reuseFailAlloc_1661_, sizeof(void*)*13 + 1, v_backend_1652_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_moreLinkArgs___proj___lam__2(lean_object* v_f_1664_, lean_object* v_cfg_1665_){
_start:
{
uint8_t v_buildType_1666_; lean_object* v_leanOptions_1667_; lean_object* v_moreLeanArgs_1668_; lean_object* v_weakLeanArgs_1669_; lean_object* v_moreLeancArgs_1670_; lean_object* v_moreServerOptions_1671_; lean_object* v_weakLeancArgs_1672_; lean_object* v_moreLinkObjs_1673_; lean_object* v_moreLinkLibs_1674_; lean_object* v_moreLinkArgs_1675_; lean_object* v_weakLinkArgs_1676_; uint8_t v_backend_1677_; lean_object* v_platformIndependent_1678_; lean_object* v_dynlibs_1679_; lean_object* v_plugins_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
v_buildType_1666_ = lean_ctor_get_uint8(v_cfg_1665_, sizeof(void*)*13);
v_leanOptions_1667_ = lean_ctor_get(v_cfg_1665_, 0);
v_moreLeanArgs_1668_ = lean_ctor_get(v_cfg_1665_, 1);
v_weakLeanArgs_1669_ = lean_ctor_get(v_cfg_1665_, 2);
v_moreLeancArgs_1670_ = lean_ctor_get(v_cfg_1665_, 3);
v_moreServerOptions_1671_ = lean_ctor_get(v_cfg_1665_, 4);
v_weakLeancArgs_1672_ = lean_ctor_get(v_cfg_1665_, 5);
v_moreLinkObjs_1673_ = lean_ctor_get(v_cfg_1665_, 6);
v_moreLinkLibs_1674_ = lean_ctor_get(v_cfg_1665_, 7);
v_moreLinkArgs_1675_ = lean_ctor_get(v_cfg_1665_, 8);
v_weakLinkArgs_1676_ = lean_ctor_get(v_cfg_1665_, 9);
v_backend_1677_ = lean_ctor_get_uint8(v_cfg_1665_, sizeof(void*)*13 + 1);
v_platformIndependent_1678_ = lean_ctor_get(v_cfg_1665_, 10);
v_dynlibs_1679_ = lean_ctor_get(v_cfg_1665_, 11);
v_plugins_1680_ = lean_ctor_get(v_cfg_1665_, 12);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_cfg_1665_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1682_ = v_cfg_1665_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_plugins_1680_);
lean_inc(v_dynlibs_1679_);
lean_inc(v_platformIndependent_1678_);
lean_inc(v_weakLinkArgs_1676_);
lean_inc(v_moreLinkArgs_1675_);
lean_inc(v_moreLinkLibs_1674_);
lean_inc(v_moreLinkObjs_1673_);
lean_inc(v_weakLeancArgs_1672_);
lean_inc(v_moreServerOptions_1671_);
lean_inc(v_moreLeancArgs_1670_);
lean_inc(v_weakLeanArgs_1669_);
lean_inc(v_moreLeanArgs_1668_);
lean_inc(v_leanOptions_1667_);
lean_dec(v_cfg_1665_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_apply_1(v_f_1664_, v_moreLinkArgs_1675_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 8, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_leanOptions_1667_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_moreLeanArgs_1668_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_weakLeanArgs_1669_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_moreLeancArgs_1670_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_moreServerOptions_1671_);
lean_ctor_set(v_reuseFailAlloc_1687_, 5, v_weakLeancArgs_1672_);
lean_ctor_set(v_reuseFailAlloc_1687_, 6, v_moreLinkObjs_1673_);
lean_ctor_set(v_reuseFailAlloc_1687_, 7, v_moreLinkLibs_1674_);
lean_ctor_set(v_reuseFailAlloc_1687_, 8, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 9, v_weakLinkArgs_1676_);
lean_ctor_set(v_reuseFailAlloc_1687_, 10, v_platformIndependent_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 11, v_dynlibs_1679_);
lean_ctor_set(v_reuseFailAlloc_1687_, 12, v_plugins_1680_);
lean_ctor_set_uint8(v_reuseFailAlloc_1687_, sizeof(void*)*13, v_buildType_1666_);
lean_ctor_set_uint8(v_reuseFailAlloc_1687_, sizeof(void*)*13 + 1, v_backend_1677_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(lean_object* v_cfg_1699_){
_start:
{
lean_object* v_weakLinkArgs_1700_; 
v_weakLinkArgs_1700_ = lean_ctor_get(v_cfg_1699_, 9);
lean_inc_ref(v_weakLinkArgs_1700_);
return v_weakLinkArgs_1700_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__0___boxed(lean_object* v_cfg_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lake_LeanConfig_weakLinkArgs___proj___lam__0(v_cfg_1701_);
lean_dec_ref(v_cfg_1701_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__1(lean_object* v_val_1703_, lean_object* v_cfg_1704_){
_start:
{
uint8_t v_buildType_1705_; lean_object* v_leanOptions_1706_; lean_object* v_moreLeanArgs_1707_; lean_object* v_weakLeanArgs_1708_; lean_object* v_moreLeancArgs_1709_; lean_object* v_moreServerOptions_1710_; lean_object* v_weakLeancArgs_1711_; lean_object* v_moreLinkObjs_1712_; lean_object* v_moreLinkLibs_1713_; lean_object* v_moreLinkArgs_1714_; uint8_t v_backend_1715_; lean_object* v_platformIndependent_1716_; lean_object* v_dynlibs_1717_; lean_object* v_plugins_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_buildType_1705_ = lean_ctor_get_uint8(v_cfg_1704_, sizeof(void*)*13);
v_leanOptions_1706_ = lean_ctor_get(v_cfg_1704_, 0);
v_moreLeanArgs_1707_ = lean_ctor_get(v_cfg_1704_, 1);
v_weakLeanArgs_1708_ = lean_ctor_get(v_cfg_1704_, 2);
v_moreLeancArgs_1709_ = lean_ctor_get(v_cfg_1704_, 3);
v_moreServerOptions_1710_ = lean_ctor_get(v_cfg_1704_, 4);
v_weakLeancArgs_1711_ = lean_ctor_get(v_cfg_1704_, 5);
v_moreLinkObjs_1712_ = lean_ctor_get(v_cfg_1704_, 6);
v_moreLinkLibs_1713_ = lean_ctor_get(v_cfg_1704_, 7);
v_moreLinkArgs_1714_ = lean_ctor_get(v_cfg_1704_, 8);
v_backend_1715_ = lean_ctor_get_uint8(v_cfg_1704_, sizeof(void*)*13 + 1);
v_platformIndependent_1716_ = lean_ctor_get(v_cfg_1704_, 10);
v_dynlibs_1717_ = lean_ctor_get(v_cfg_1704_, 11);
v_plugins_1718_ = lean_ctor_get(v_cfg_1704_, 12);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_cfg_1704_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v_cfg_1704_, 9);
lean_dec(v_unused_1726_);
v___x_1720_ = v_cfg_1704_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_plugins_1718_);
lean_inc(v_dynlibs_1717_);
lean_inc(v_platformIndependent_1716_);
lean_inc(v_moreLinkArgs_1714_);
lean_inc(v_moreLinkLibs_1713_);
lean_inc(v_moreLinkObjs_1712_);
lean_inc(v_weakLeancArgs_1711_);
lean_inc(v_moreServerOptions_1710_);
lean_inc(v_moreLeancArgs_1709_);
lean_inc(v_weakLeanArgs_1708_);
lean_inc(v_moreLeanArgs_1707_);
lean_inc(v_leanOptions_1706_);
lean_dec(v_cfg_1704_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 9, v_val_1703_);
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_leanOptions_1706_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_moreLeanArgs_1707_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_weakLeanArgs_1708_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_moreLeancArgs_1709_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_moreServerOptions_1710_);
lean_ctor_set(v_reuseFailAlloc_1724_, 5, v_weakLeancArgs_1711_);
lean_ctor_set(v_reuseFailAlloc_1724_, 6, v_moreLinkObjs_1712_);
lean_ctor_set(v_reuseFailAlloc_1724_, 7, v_moreLinkLibs_1713_);
lean_ctor_set(v_reuseFailAlloc_1724_, 8, v_moreLinkArgs_1714_);
lean_ctor_set(v_reuseFailAlloc_1724_, 9, v_val_1703_);
lean_ctor_set(v_reuseFailAlloc_1724_, 10, v_platformIndependent_1716_);
lean_ctor_set(v_reuseFailAlloc_1724_, 11, v_dynlibs_1717_);
lean_ctor_set(v_reuseFailAlloc_1724_, 12, v_plugins_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*13, v_buildType_1705_);
lean_ctor_set_uint8(v_reuseFailAlloc_1724_, sizeof(void*)*13 + 1, v_backend_1715_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_weakLinkArgs___proj___lam__2(lean_object* v_f_1727_, lean_object* v_cfg_1728_){
_start:
{
uint8_t v_buildType_1729_; lean_object* v_leanOptions_1730_; lean_object* v_moreLeanArgs_1731_; lean_object* v_weakLeanArgs_1732_; lean_object* v_moreLeancArgs_1733_; lean_object* v_moreServerOptions_1734_; lean_object* v_weakLeancArgs_1735_; lean_object* v_moreLinkObjs_1736_; lean_object* v_moreLinkLibs_1737_; lean_object* v_moreLinkArgs_1738_; lean_object* v_weakLinkArgs_1739_; uint8_t v_backend_1740_; lean_object* v_platformIndependent_1741_; lean_object* v_dynlibs_1742_; lean_object* v_plugins_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1751_; 
v_buildType_1729_ = lean_ctor_get_uint8(v_cfg_1728_, sizeof(void*)*13);
v_leanOptions_1730_ = lean_ctor_get(v_cfg_1728_, 0);
v_moreLeanArgs_1731_ = lean_ctor_get(v_cfg_1728_, 1);
v_weakLeanArgs_1732_ = lean_ctor_get(v_cfg_1728_, 2);
v_moreLeancArgs_1733_ = lean_ctor_get(v_cfg_1728_, 3);
v_moreServerOptions_1734_ = lean_ctor_get(v_cfg_1728_, 4);
v_weakLeancArgs_1735_ = lean_ctor_get(v_cfg_1728_, 5);
v_moreLinkObjs_1736_ = lean_ctor_get(v_cfg_1728_, 6);
v_moreLinkLibs_1737_ = lean_ctor_get(v_cfg_1728_, 7);
v_moreLinkArgs_1738_ = lean_ctor_get(v_cfg_1728_, 8);
v_weakLinkArgs_1739_ = lean_ctor_get(v_cfg_1728_, 9);
v_backend_1740_ = lean_ctor_get_uint8(v_cfg_1728_, sizeof(void*)*13 + 1);
v_platformIndependent_1741_ = lean_ctor_get(v_cfg_1728_, 10);
v_dynlibs_1742_ = lean_ctor_get(v_cfg_1728_, 11);
v_plugins_1743_ = lean_ctor_get(v_cfg_1728_, 12);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_cfg_1728_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1745_ = v_cfg_1728_;
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_plugins_1743_);
lean_inc(v_dynlibs_1742_);
lean_inc(v_platformIndependent_1741_);
lean_inc(v_weakLinkArgs_1739_);
lean_inc(v_moreLinkArgs_1738_);
lean_inc(v_moreLinkLibs_1737_);
lean_inc(v_moreLinkObjs_1736_);
lean_inc(v_weakLeancArgs_1735_);
lean_inc(v_moreServerOptions_1734_);
lean_inc(v_moreLeancArgs_1733_);
lean_inc(v_weakLeanArgs_1732_);
lean_inc(v_moreLeanArgs_1731_);
lean_inc(v_leanOptions_1730_);
lean_dec(v_cfg_1728_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1751_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_apply_1(v_f_1727_, v_weakLinkArgs_1739_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 9, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_leanOptions_1730_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_moreLeanArgs_1731_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_weakLeanArgs_1732_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_moreLeancArgs_1733_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_moreServerOptions_1734_);
lean_ctor_set(v_reuseFailAlloc_1750_, 5, v_weakLeancArgs_1735_);
lean_ctor_set(v_reuseFailAlloc_1750_, 6, v_moreLinkObjs_1736_);
lean_ctor_set(v_reuseFailAlloc_1750_, 7, v_moreLinkLibs_1737_);
lean_ctor_set(v_reuseFailAlloc_1750_, 8, v_moreLinkArgs_1738_);
lean_ctor_set(v_reuseFailAlloc_1750_, 9, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1750_, 10, v_platformIndependent_1741_);
lean_ctor_set(v_reuseFailAlloc_1750_, 11, v_dynlibs_1742_);
lean_ctor_set(v_reuseFailAlloc_1750_, 12, v_plugins_1743_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*13, v_buildType_1729_);
lean_ctor_set_uint8(v_reuseFailAlloc_1750_, sizeof(void*)*13 + 1, v_backend_1740_);
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
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__0(lean_object* v_cfg_1762_){
_start:
{
uint8_t v_backend_1763_; 
v_backend_1763_ = lean_ctor_get_uint8(v_cfg_1762_, sizeof(void*)*13 + 1);
return v_backend_1763_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__0___boxed(lean_object* v_cfg_1764_){
_start:
{
uint8_t v_res_1765_; lean_object* v_r_1766_; 
v_res_1765_ = l_Lake_LeanConfig_backend___proj___lam__0(v_cfg_1764_);
lean_dec_ref(v_cfg_1764_);
v_r_1766_ = lean_box(v_res_1765_);
return v_r_1766_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1(uint8_t v_val_1767_, lean_object* v_cfg_1768_){
_start:
{
uint8_t v_buildType_1769_; lean_object* v_leanOptions_1770_; lean_object* v_moreLeanArgs_1771_; lean_object* v_weakLeanArgs_1772_; lean_object* v_moreLeancArgs_1773_; lean_object* v_moreServerOptions_1774_; lean_object* v_weakLeancArgs_1775_; lean_object* v_moreLinkObjs_1776_; lean_object* v_moreLinkLibs_1777_; lean_object* v_moreLinkArgs_1778_; lean_object* v_weakLinkArgs_1779_; lean_object* v_platformIndependent_1780_; lean_object* v_dynlibs_1781_; lean_object* v_plugins_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
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
v_weakLinkArgs_1779_ = lean_ctor_get(v_cfg_1768_, 9);
v_platformIndependent_1780_ = lean_ctor_get(v_cfg_1768_, 10);
v_dynlibs_1781_ = lean_ctor_get(v_cfg_1768_, 11);
v_plugins_1782_ = lean_ctor_get(v_cfg_1768_, 12);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_cfg_1768_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v_cfg_1768_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_plugins_1782_);
lean_inc(v_dynlibs_1781_);
lean_inc(v_platformIndependent_1780_);
lean_inc(v_weakLinkArgs_1779_);
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
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_leanOptions_1770_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_moreLeanArgs_1771_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_weakLeanArgs_1772_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_moreLeancArgs_1773_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_moreServerOptions_1774_);
lean_ctor_set(v_reuseFailAlloc_1788_, 5, v_weakLeancArgs_1775_);
lean_ctor_set(v_reuseFailAlloc_1788_, 6, v_moreLinkObjs_1776_);
lean_ctor_set(v_reuseFailAlloc_1788_, 7, v_moreLinkLibs_1777_);
lean_ctor_set(v_reuseFailAlloc_1788_, 8, v_moreLinkArgs_1778_);
lean_ctor_set(v_reuseFailAlloc_1788_, 9, v_weakLinkArgs_1779_);
lean_ctor_set(v_reuseFailAlloc_1788_, 10, v_platformIndependent_1780_);
lean_ctor_set(v_reuseFailAlloc_1788_, 11, v_dynlibs_1781_);
lean_ctor_set(v_reuseFailAlloc_1788_, 12, v_plugins_1782_);
lean_ctor_set_uint8(v_reuseFailAlloc_1788_, sizeof(void*)*13, v_buildType_1769_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_ctor_set_uint8(v___x_1787_, sizeof(void*)*13 + 1, v_val_1767_);
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__1___boxed(lean_object* v_val_1790_, lean_object* v_cfg_1791_){
_start:
{
uint8_t v_val_79__boxed_1792_; lean_object* v_res_1793_; 
v_val_79__boxed_1792_ = lean_unbox(v_val_1790_);
v_res_1793_ = l_Lake_LeanConfig_backend___proj___lam__1(v_val_79__boxed_1792_, v_cfg_1791_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__2(lean_object* v_f_1794_, lean_object* v_cfg_1795_){
_start:
{
uint8_t v_buildType_1796_; lean_object* v_leanOptions_1797_; lean_object* v_moreLeanArgs_1798_; lean_object* v_weakLeanArgs_1799_; lean_object* v_moreLeancArgs_1800_; lean_object* v_moreServerOptions_1801_; lean_object* v_weakLeancArgs_1802_; lean_object* v_moreLinkObjs_1803_; lean_object* v_moreLinkLibs_1804_; lean_object* v_moreLinkArgs_1805_; lean_object* v_weakLinkArgs_1806_; uint8_t v_backend_1807_; lean_object* v_platformIndependent_1808_; lean_object* v_dynlibs_1809_; lean_object* v_plugins_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1820_; 
v_buildType_1796_ = lean_ctor_get_uint8(v_cfg_1795_, sizeof(void*)*13);
v_leanOptions_1797_ = lean_ctor_get(v_cfg_1795_, 0);
v_moreLeanArgs_1798_ = lean_ctor_get(v_cfg_1795_, 1);
v_weakLeanArgs_1799_ = lean_ctor_get(v_cfg_1795_, 2);
v_moreLeancArgs_1800_ = lean_ctor_get(v_cfg_1795_, 3);
v_moreServerOptions_1801_ = lean_ctor_get(v_cfg_1795_, 4);
v_weakLeancArgs_1802_ = lean_ctor_get(v_cfg_1795_, 5);
v_moreLinkObjs_1803_ = lean_ctor_get(v_cfg_1795_, 6);
v_moreLinkLibs_1804_ = lean_ctor_get(v_cfg_1795_, 7);
v_moreLinkArgs_1805_ = lean_ctor_get(v_cfg_1795_, 8);
v_weakLinkArgs_1806_ = lean_ctor_get(v_cfg_1795_, 9);
v_backend_1807_ = lean_ctor_get_uint8(v_cfg_1795_, sizeof(void*)*13 + 1);
v_platformIndependent_1808_ = lean_ctor_get(v_cfg_1795_, 10);
v_dynlibs_1809_ = lean_ctor_get(v_cfg_1795_, 11);
v_plugins_1810_ = lean_ctor_get(v_cfg_1795_, 12);
v_isSharedCheck_1820_ = !lean_is_exclusive(v_cfg_1795_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1812_ = v_cfg_1795_;
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_plugins_1810_);
lean_inc(v_dynlibs_1809_);
lean_inc(v_platformIndependent_1808_);
lean_inc(v_weakLinkArgs_1806_);
lean_inc(v_moreLinkArgs_1805_);
lean_inc(v_moreLinkLibs_1804_);
lean_inc(v_moreLinkObjs_1803_);
lean_inc(v_weakLeancArgs_1802_);
lean_inc(v_moreServerOptions_1801_);
lean_inc(v_moreLeancArgs_1800_);
lean_inc(v_weakLeanArgs_1799_);
lean_inc(v_moreLeanArgs_1798_);
lean_inc(v_leanOptions_1797_);
lean_dec(v_cfg_1795_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1820_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1814_ = lean_box(v_backend_1807_);
v___x_1815_ = lean_apply_1(v_f_1794_, v___x_1814_);
if (v_isShared_1813_ == 0)
{
v___x_1817_ = v___x_1812_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_leanOptions_1797_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v_moreLeanArgs_1798_);
lean_ctor_set(v_reuseFailAlloc_1819_, 2, v_weakLeanArgs_1799_);
lean_ctor_set(v_reuseFailAlloc_1819_, 3, v_moreLeancArgs_1800_);
lean_ctor_set(v_reuseFailAlloc_1819_, 4, v_moreServerOptions_1801_);
lean_ctor_set(v_reuseFailAlloc_1819_, 5, v_weakLeancArgs_1802_);
lean_ctor_set(v_reuseFailAlloc_1819_, 6, v_moreLinkObjs_1803_);
lean_ctor_set(v_reuseFailAlloc_1819_, 7, v_moreLinkLibs_1804_);
lean_ctor_set(v_reuseFailAlloc_1819_, 8, v_moreLinkArgs_1805_);
lean_ctor_set(v_reuseFailAlloc_1819_, 9, v_weakLinkArgs_1806_);
lean_ctor_set(v_reuseFailAlloc_1819_, 10, v_platformIndependent_1808_);
lean_ctor_set(v_reuseFailAlloc_1819_, 11, v_dynlibs_1809_);
lean_ctor_set(v_reuseFailAlloc_1819_, 12, v_plugins_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1819_, sizeof(void*)*13, v_buildType_1796_);
v___x_1817_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_unbox(v___x_1815_);
lean_ctor_set_uint8(v___x_1817_, sizeof(void*)*13 + 1, v___x_1818_);
return v___x_1817_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_LeanConfig_backend___proj___lam__3(lean_object* v_x_1821_){
_start:
{
uint8_t v___x_1822_; 
v___x_1822_ = 2;
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_backend___proj___lam__3___boxed(lean_object* v_x_1823_){
_start:
{
uint8_t v_res_1824_; lean_object* v_r_1825_; 
v_res_1824_ = l_Lake_LeanConfig_backend___proj___lam__3(v_x_1823_);
lean_dec_ref(v_x_1823_);
v_r_1825_ = lean_box(v_res_1824_);
return v_r_1825_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0(lean_object* v_cfg_1837_){
_start:
{
lean_object* v_platformIndependent_1838_; 
v_platformIndependent_1838_ = lean_ctor_get(v_cfg_1837_, 10);
lean_inc(v_platformIndependent_1838_);
return v_platformIndependent_1838_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__0___boxed(lean_object* v_cfg_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lake_LeanConfig_platformIndependent___proj___lam__0(v_cfg_1839_);
lean_dec_ref(v_cfg_1839_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__1(lean_object* v_val_1841_, lean_object* v_cfg_1842_){
_start:
{
uint8_t v_buildType_1843_; lean_object* v_leanOptions_1844_; lean_object* v_moreLeanArgs_1845_; lean_object* v_weakLeanArgs_1846_; lean_object* v_moreLeancArgs_1847_; lean_object* v_moreServerOptions_1848_; lean_object* v_weakLeancArgs_1849_; lean_object* v_moreLinkObjs_1850_; lean_object* v_moreLinkLibs_1851_; lean_object* v_moreLinkArgs_1852_; lean_object* v_weakLinkArgs_1853_; uint8_t v_backend_1854_; lean_object* v_dynlibs_1855_; lean_object* v_plugins_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
v_buildType_1843_ = lean_ctor_get_uint8(v_cfg_1842_, sizeof(void*)*13);
v_leanOptions_1844_ = lean_ctor_get(v_cfg_1842_, 0);
v_moreLeanArgs_1845_ = lean_ctor_get(v_cfg_1842_, 1);
v_weakLeanArgs_1846_ = lean_ctor_get(v_cfg_1842_, 2);
v_moreLeancArgs_1847_ = lean_ctor_get(v_cfg_1842_, 3);
v_moreServerOptions_1848_ = lean_ctor_get(v_cfg_1842_, 4);
v_weakLeancArgs_1849_ = lean_ctor_get(v_cfg_1842_, 5);
v_moreLinkObjs_1850_ = lean_ctor_get(v_cfg_1842_, 6);
v_moreLinkLibs_1851_ = lean_ctor_get(v_cfg_1842_, 7);
v_moreLinkArgs_1852_ = lean_ctor_get(v_cfg_1842_, 8);
v_weakLinkArgs_1853_ = lean_ctor_get(v_cfg_1842_, 9);
v_backend_1854_ = lean_ctor_get_uint8(v_cfg_1842_, sizeof(void*)*13 + 1);
v_dynlibs_1855_ = lean_ctor_get(v_cfg_1842_, 11);
v_plugins_1856_ = lean_ctor_get(v_cfg_1842_, 12);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_cfg_1842_);
if (v_isSharedCheck_1863_ == 0)
{
lean_object* v_unused_1864_; 
v_unused_1864_ = lean_ctor_get(v_cfg_1842_, 10);
lean_dec(v_unused_1864_);
v___x_1858_ = v_cfg_1842_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_plugins_1856_);
lean_inc(v_dynlibs_1855_);
lean_inc(v_weakLinkArgs_1853_);
lean_inc(v_moreLinkArgs_1852_);
lean_inc(v_moreLinkLibs_1851_);
lean_inc(v_moreLinkObjs_1850_);
lean_inc(v_weakLeancArgs_1849_);
lean_inc(v_moreServerOptions_1848_);
lean_inc(v_moreLeancArgs_1847_);
lean_inc(v_weakLeanArgs_1846_);
lean_inc(v_moreLeanArgs_1845_);
lean_inc(v_leanOptions_1844_);
lean_dec(v_cfg_1842_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 10, v_val_1841_);
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_leanOptions_1844_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_moreLeanArgs_1845_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v_weakLeanArgs_1846_);
lean_ctor_set(v_reuseFailAlloc_1862_, 3, v_moreLeancArgs_1847_);
lean_ctor_set(v_reuseFailAlloc_1862_, 4, v_moreServerOptions_1848_);
lean_ctor_set(v_reuseFailAlloc_1862_, 5, v_weakLeancArgs_1849_);
lean_ctor_set(v_reuseFailAlloc_1862_, 6, v_moreLinkObjs_1850_);
lean_ctor_set(v_reuseFailAlloc_1862_, 7, v_moreLinkLibs_1851_);
lean_ctor_set(v_reuseFailAlloc_1862_, 8, v_moreLinkArgs_1852_);
lean_ctor_set(v_reuseFailAlloc_1862_, 9, v_weakLinkArgs_1853_);
lean_ctor_set(v_reuseFailAlloc_1862_, 10, v_val_1841_);
lean_ctor_set(v_reuseFailAlloc_1862_, 11, v_dynlibs_1855_);
lean_ctor_set(v_reuseFailAlloc_1862_, 12, v_plugins_1856_);
lean_ctor_set_uint8(v_reuseFailAlloc_1862_, sizeof(void*)*13, v_buildType_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1862_, sizeof(void*)*13 + 1, v_backend_1854_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__2(lean_object* v_f_1865_, lean_object* v_cfg_1866_){
_start:
{
uint8_t v_buildType_1867_; lean_object* v_leanOptions_1868_; lean_object* v_moreLeanArgs_1869_; lean_object* v_weakLeanArgs_1870_; lean_object* v_moreLeancArgs_1871_; lean_object* v_moreServerOptions_1872_; lean_object* v_weakLeancArgs_1873_; lean_object* v_moreLinkObjs_1874_; lean_object* v_moreLinkLibs_1875_; lean_object* v_moreLinkArgs_1876_; lean_object* v_weakLinkArgs_1877_; uint8_t v_backend_1878_; lean_object* v_platformIndependent_1879_; lean_object* v_dynlibs_1880_; lean_object* v_plugins_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1889_; 
v_buildType_1867_ = lean_ctor_get_uint8(v_cfg_1866_, sizeof(void*)*13);
v_leanOptions_1868_ = lean_ctor_get(v_cfg_1866_, 0);
v_moreLeanArgs_1869_ = lean_ctor_get(v_cfg_1866_, 1);
v_weakLeanArgs_1870_ = lean_ctor_get(v_cfg_1866_, 2);
v_moreLeancArgs_1871_ = lean_ctor_get(v_cfg_1866_, 3);
v_moreServerOptions_1872_ = lean_ctor_get(v_cfg_1866_, 4);
v_weakLeancArgs_1873_ = lean_ctor_get(v_cfg_1866_, 5);
v_moreLinkObjs_1874_ = lean_ctor_get(v_cfg_1866_, 6);
v_moreLinkLibs_1875_ = lean_ctor_get(v_cfg_1866_, 7);
v_moreLinkArgs_1876_ = lean_ctor_get(v_cfg_1866_, 8);
v_weakLinkArgs_1877_ = lean_ctor_get(v_cfg_1866_, 9);
v_backend_1878_ = lean_ctor_get_uint8(v_cfg_1866_, sizeof(void*)*13 + 1);
v_platformIndependent_1879_ = lean_ctor_get(v_cfg_1866_, 10);
v_dynlibs_1880_ = lean_ctor_get(v_cfg_1866_, 11);
v_plugins_1881_ = lean_ctor_get(v_cfg_1866_, 12);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_cfg_1866_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1883_ = v_cfg_1866_;
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_plugins_1881_);
lean_inc(v_dynlibs_1880_);
lean_inc(v_platformIndependent_1879_);
lean_inc(v_weakLinkArgs_1877_);
lean_inc(v_moreLinkArgs_1876_);
lean_inc(v_moreLinkLibs_1875_);
lean_inc(v_moreLinkObjs_1874_);
lean_inc(v_weakLeancArgs_1873_);
lean_inc(v_moreServerOptions_1872_);
lean_inc(v_moreLeancArgs_1871_);
lean_inc(v_weakLeanArgs_1870_);
lean_inc(v_moreLeanArgs_1869_);
lean_inc(v_leanOptions_1868_);
lean_dec(v_cfg_1866_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1889_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1885_ = lean_apply_1(v_f_1865_, v_platformIndependent_1879_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 10, v___x_1885_);
v___x_1887_ = v___x_1883_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_leanOptions_1868_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_moreLeanArgs_1869_);
lean_ctor_set(v_reuseFailAlloc_1888_, 2, v_weakLeanArgs_1870_);
lean_ctor_set(v_reuseFailAlloc_1888_, 3, v_moreLeancArgs_1871_);
lean_ctor_set(v_reuseFailAlloc_1888_, 4, v_moreServerOptions_1872_);
lean_ctor_set(v_reuseFailAlloc_1888_, 5, v_weakLeancArgs_1873_);
lean_ctor_set(v_reuseFailAlloc_1888_, 6, v_moreLinkObjs_1874_);
lean_ctor_set(v_reuseFailAlloc_1888_, 7, v_moreLinkLibs_1875_);
lean_ctor_set(v_reuseFailAlloc_1888_, 8, v_moreLinkArgs_1876_);
lean_ctor_set(v_reuseFailAlloc_1888_, 9, v_weakLinkArgs_1877_);
lean_ctor_set(v_reuseFailAlloc_1888_, 10, v___x_1885_);
lean_ctor_set(v_reuseFailAlloc_1888_, 11, v_dynlibs_1880_);
lean_ctor_set(v_reuseFailAlloc_1888_, 12, v_plugins_1881_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13, v_buildType_1867_);
lean_ctor_set_uint8(v_reuseFailAlloc_1888_, sizeof(void*)*13 + 1, v_backend_1878_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3(lean_object* v_x_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_box(0);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_platformIndependent___proj___lam__3___boxed(lean_object* v_x_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lake_LeanConfig_platformIndependent___proj___lam__3(v_x_1892_);
lean_dec_ref(v_x_1892_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0(lean_object* v_cfg_1905_){
_start:
{
lean_object* v_dynlibs_1906_; 
v_dynlibs_1906_ = lean_ctor_get(v_cfg_1905_, 11);
lean_inc_ref(v_dynlibs_1906_);
return v_dynlibs_1906_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__0___boxed(lean_object* v_cfg_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lake_LeanConfig_dynlibs___proj___lam__0(v_cfg_1907_);
lean_dec_ref(v_cfg_1907_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__1(lean_object* v_val_1909_, lean_object* v_cfg_1910_){
_start:
{
uint8_t v_buildType_1911_; lean_object* v_leanOptions_1912_; lean_object* v_moreLeanArgs_1913_; lean_object* v_weakLeanArgs_1914_; lean_object* v_moreLeancArgs_1915_; lean_object* v_moreServerOptions_1916_; lean_object* v_weakLeancArgs_1917_; lean_object* v_moreLinkObjs_1918_; lean_object* v_moreLinkLibs_1919_; lean_object* v_moreLinkArgs_1920_; lean_object* v_weakLinkArgs_1921_; uint8_t v_backend_1922_; lean_object* v_platformIndependent_1923_; lean_object* v_plugins_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
v_buildType_1911_ = lean_ctor_get_uint8(v_cfg_1910_, sizeof(void*)*13);
v_leanOptions_1912_ = lean_ctor_get(v_cfg_1910_, 0);
v_moreLeanArgs_1913_ = lean_ctor_get(v_cfg_1910_, 1);
v_weakLeanArgs_1914_ = lean_ctor_get(v_cfg_1910_, 2);
v_moreLeancArgs_1915_ = lean_ctor_get(v_cfg_1910_, 3);
v_moreServerOptions_1916_ = lean_ctor_get(v_cfg_1910_, 4);
v_weakLeancArgs_1917_ = lean_ctor_get(v_cfg_1910_, 5);
v_moreLinkObjs_1918_ = lean_ctor_get(v_cfg_1910_, 6);
v_moreLinkLibs_1919_ = lean_ctor_get(v_cfg_1910_, 7);
v_moreLinkArgs_1920_ = lean_ctor_get(v_cfg_1910_, 8);
v_weakLinkArgs_1921_ = lean_ctor_get(v_cfg_1910_, 9);
v_backend_1922_ = lean_ctor_get_uint8(v_cfg_1910_, sizeof(void*)*13 + 1);
v_platformIndependent_1923_ = lean_ctor_get(v_cfg_1910_, 10);
v_plugins_1924_ = lean_ctor_get(v_cfg_1910_, 12);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_cfg_1910_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_cfg_1910_, 11);
lean_dec(v_unused_1932_);
v___x_1926_ = v_cfg_1910_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_plugins_1924_);
lean_inc(v_platformIndependent_1923_);
lean_inc(v_weakLinkArgs_1921_);
lean_inc(v_moreLinkArgs_1920_);
lean_inc(v_moreLinkLibs_1919_);
lean_inc(v_moreLinkObjs_1918_);
lean_inc(v_weakLeancArgs_1917_);
lean_inc(v_moreServerOptions_1916_);
lean_inc(v_moreLeancArgs_1915_);
lean_inc(v_weakLeanArgs_1914_);
lean_inc(v_moreLeanArgs_1913_);
lean_inc(v_leanOptions_1912_);
lean_dec(v_cfg_1910_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 11, v_val_1909_);
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_leanOptions_1912_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_moreLeanArgs_1913_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_weakLeanArgs_1914_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_moreLeancArgs_1915_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_moreServerOptions_1916_);
lean_ctor_set(v_reuseFailAlloc_1930_, 5, v_weakLeancArgs_1917_);
lean_ctor_set(v_reuseFailAlloc_1930_, 6, v_moreLinkObjs_1918_);
lean_ctor_set(v_reuseFailAlloc_1930_, 7, v_moreLinkLibs_1919_);
lean_ctor_set(v_reuseFailAlloc_1930_, 8, v_moreLinkArgs_1920_);
lean_ctor_set(v_reuseFailAlloc_1930_, 9, v_weakLinkArgs_1921_);
lean_ctor_set(v_reuseFailAlloc_1930_, 10, v_platformIndependent_1923_);
lean_ctor_set(v_reuseFailAlloc_1930_, 11, v_val_1909_);
lean_ctor_set(v_reuseFailAlloc_1930_, 12, v_plugins_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13, v_buildType_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1930_, sizeof(void*)*13 + 1, v_backend_1922_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_dynlibs___proj___lam__2(lean_object* v_f_1933_, lean_object* v_cfg_1934_){
_start:
{
uint8_t v_buildType_1935_; lean_object* v_leanOptions_1936_; lean_object* v_moreLeanArgs_1937_; lean_object* v_weakLeanArgs_1938_; lean_object* v_moreLeancArgs_1939_; lean_object* v_moreServerOptions_1940_; lean_object* v_weakLeancArgs_1941_; lean_object* v_moreLinkObjs_1942_; lean_object* v_moreLinkLibs_1943_; lean_object* v_moreLinkArgs_1944_; lean_object* v_weakLinkArgs_1945_; uint8_t v_backend_1946_; lean_object* v_platformIndependent_1947_; lean_object* v_dynlibs_1948_; lean_object* v_plugins_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1957_; 
v_buildType_1935_ = lean_ctor_get_uint8(v_cfg_1934_, sizeof(void*)*13);
v_leanOptions_1936_ = lean_ctor_get(v_cfg_1934_, 0);
v_moreLeanArgs_1937_ = lean_ctor_get(v_cfg_1934_, 1);
v_weakLeanArgs_1938_ = lean_ctor_get(v_cfg_1934_, 2);
v_moreLeancArgs_1939_ = lean_ctor_get(v_cfg_1934_, 3);
v_moreServerOptions_1940_ = lean_ctor_get(v_cfg_1934_, 4);
v_weakLeancArgs_1941_ = lean_ctor_get(v_cfg_1934_, 5);
v_moreLinkObjs_1942_ = lean_ctor_get(v_cfg_1934_, 6);
v_moreLinkLibs_1943_ = lean_ctor_get(v_cfg_1934_, 7);
v_moreLinkArgs_1944_ = lean_ctor_get(v_cfg_1934_, 8);
v_weakLinkArgs_1945_ = lean_ctor_get(v_cfg_1934_, 9);
v_backend_1946_ = lean_ctor_get_uint8(v_cfg_1934_, sizeof(void*)*13 + 1);
v_platformIndependent_1947_ = lean_ctor_get(v_cfg_1934_, 10);
v_dynlibs_1948_ = lean_ctor_get(v_cfg_1934_, 11);
v_plugins_1949_ = lean_ctor_get(v_cfg_1934_, 12);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_cfg_1934_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1951_ = v_cfg_1934_;
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_plugins_1949_);
lean_inc(v_dynlibs_1948_);
lean_inc(v_platformIndependent_1947_);
lean_inc(v_weakLinkArgs_1945_);
lean_inc(v_moreLinkArgs_1944_);
lean_inc(v_moreLinkLibs_1943_);
lean_inc(v_moreLinkObjs_1942_);
lean_inc(v_weakLeancArgs_1941_);
lean_inc(v_moreServerOptions_1940_);
lean_inc(v_moreLeancArgs_1939_);
lean_inc(v_weakLeanArgs_1938_);
lean_inc(v_moreLeanArgs_1937_);
lean_inc(v_leanOptions_1936_);
lean_dec(v_cfg_1934_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1957_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = lean_apply_1(v_f_1933_, v_dynlibs_1948_);
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 11, v___x_1953_);
v___x_1955_ = v___x_1951_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_leanOptions_1936_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_moreLeanArgs_1937_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v_weakLeanArgs_1938_);
lean_ctor_set(v_reuseFailAlloc_1956_, 3, v_moreLeancArgs_1939_);
lean_ctor_set(v_reuseFailAlloc_1956_, 4, v_moreServerOptions_1940_);
lean_ctor_set(v_reuseFailAlloc_1956_, 5, v_weakLeancArgs_1941_);
lean_ctor_set(v_reuseFailAlloc_1956_, 6, v_moreLinkObjs_1942_);
lean_ctor_set(v_reuseFailAlloc_1956_, 7, v_moreLinkLibs_1943_);
lean_ctor_set(v_reuseFailAlloc_1956_, 8, v_moreLinkArgs_1944_);
lean_ctor_set(v_reuseFailAlloc_1956_, 9, v_weakLinkArgs_1945_);
lean_ctor_set(v_reuseFailAlloc_1956_, 10, v_platformIndependent_1947_);
lean_ctor_set(v_reuseFailAlloc_1956_, 11, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1956_, 12, v_plugins_1949_);
lean_ctor_set_uint8(v_reuseFailAlloc_1956_, sizeof(void*)*13, v_buildType_1935_);
lean_ctor_set_uint8(v_reuseFailAlloc_1956_, sizeof(void*)*13 + 1, v_backend_1946_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0(lean_object* v_cfg_1968_){
_start:
{
lean_object* v_plugins_1969_; 
v_plugins_1969_ = lean_ctor_get(v_cfg_1968_, 12);
lean_inc_ref(v_plugins_1969_);
return v_plugins_1969_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__0___boxed(lean_object* v_cfg_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lake_LeanConfig_plugins___proj___lam__0(v_cfg_1970_);
lean_dec_ref(v_cfg_1970_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__1(lean_object* v_val_1972_, lean_object* v_cfg_1973_){
_start:
{
uint8_t v_buildType_1974_; lean_object* v_leanOptions_1975_; lean_object* v_moreLeanArgs_1976_; lean_object* v_weakLeanArgs_1977_; lean_object* v_moreLeancArgs_1978_; lean_object* v_moreServerOptions_1979_; lean_object* v_weakLeancArgs_1980_; lean_object* v_moreLinkObjs_1981_; lean_object* v_moreLinkLibs_1982_; lean_object* v_moreLinkArgs_1983_; lean_object* v_weakLinkArgs_1984_; uint8_t v_backend_1985_; lean_object* v_platformIndependent_1986_; lean_object* v_dynlibs_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_buildType_1974_ = lean_ctor_get_uint8(v_cfg_1973_, sizeof(void*)*13);
v_leanOptions_1975_ = lean_ctor_get(v_cfg_1973_, 0);
v_moreLeanArgs_1976_ = lean_ctor_get(v_cfg_1973_, 1);
v_weakLeanArgs_1977_ = lean_ctor_get(v_cfg_1973_, 2);
v_moreLeancArgs_1978_ = lean_ctor_get(v_cfg_1973_, 3);
v_moreServerOptions_1979_ = lean_ctor_get(v_cfg_1973_, 4);
v_weakLeancArgs_1980_ = lean_ctor_get(v_cfg_1973_, 5);
v_moreLinkObjs_1981_ = lean_ctor_get(v_cfg_1973_, 6);
v_moreLinkLibs_1982_ = lean_ctor_get(v_cfg_1973_, 7);
v_moreLinkArgs_1983_ = lean_ctor_get(v_cfg_1973_, 8);
v_weakLinkArgs_1984_ = lean_ctor_get(v_cfg_1973_, 9);
v_backend_1985_ = lean_ctor_get_uint8(v_cfg_1973_, sizeof(void*)*13 + 1);
v_platformIndependent_1986_ = lean_ctor_get(v_cfg_1973_, 10);
v_dynlibs_1987_ = lean_ctor_get(v_cfg_1973_, 11);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_cfg_1973_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v_cfg_1973_, 12);
lean_dec(v_unused_1995_);
v___x_1989_ = v_cfg_1973_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_dynlibs_1987_);
lean_inc(v_platformIndependent_1986_);
lean_inc(v_weakLinkArgs_1984_);
lean_inc(v_moreLinkArgs_1983_);
lean_inc(v_moreLinkLibs_1982_);
lean_inc(v_moreLinkObjs_1981_);
lean_inc(v_weakLeancArgs_1980_);
lean_inc(v_moreServerOptions_1979_);
lean_inc(v_moreLeancArgs_1978_);
lean_inc(v_weakLeanArgs_1977_);
lean_inc(v_moreLeanArgs_1976_);
lean_inc(v_leanOptions_1975_);
lean_dec(v_cfg_1973_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 12, v_val_1972_);
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_leanOptions_1975_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_moreLeanArgs_1976_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_weakLeanArgs_1977_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_moreLeancArgs_1978_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_moreServerOptions_1979_);
lean_ctor_set(v_reuseFailAlloc_1993_, 5, v_weakLeancArgs_1980_);
lean_ctor_set(v_reuseFailAlloc_1993_, 6, v_moreLinkObjs_1981_);
lean_ctor_set(v_reuseFailAlloc_1993_, 7, v_moreLinkLibs_1982_);
lean_ctor_set(v_reuseFailAlloc_1993_, 8, v_moreLinkArgs_1983_);
lean_ctor_set(v_reuseFailAlloc_1993_, 9, v_weakLinkArgs_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 10, v_platformIndependent_1986_);
lean_ctor_set(v_reuseFailAlloc_1993_, 11, v_dynlibs_1987_);
lean_ctor_set(v_reuseFailAlloc_1993_, 12, v_val_1972_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13, v_buildType_1974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*13 + 1, v_backend_1985_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_plugins___proj___lam__2(lean_object* v_f_1996_, lean_object* v_cfg_1997_){
_start:
{
uint8_t v_buildType_1998_; lean_object* v_leanOptions_1999_; lean_object* v_moreLeanArgs_2000_; lean_object* v_weakLeanArgs_2001_; lean_object* v_moreLeancArgs_2002_; lean_object* v_moreServerOptions_2003_; lean_object* v_weakLeancArgs_2004_; lean_object* v_moreLinkObjs_2005_; lean_object* v_moreLinkLibs_2006_; lean_object* v_moreLinkArgs_2007_; lean_object* v_weakLinkArgs_2008_; uint8_t v_backend_2009_; lean_object* v_platformIndependent_2010_; lean_object* v_dynlibs_2011_; lean_object* v_plugins_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2020_; 
v_buildType_1998_ = lean_ctor_get_uint8(v_cfg_1997_, sizeof(void*)*13);
v_leanOptions_1999_ = lean_ctor_get(v_cfg_1997_, 0);
v_moreLeanArgs_2000_ = lean_ctor_get(v_cfg_1997_, 1);
v_weakLeanArgs_2001_ = lean_ctor_get(v_cfg_1997_, 2);
v_moreLeancArgs_2002_ = lean_ctor_get(v_cfg_1997_, 3);
v_moreServerOptions_2003_ = lean_ctor_get(v_cfg_1997_, 4);
v_weakLeancArgs_2004_ = lean_ctor_get(v_cfg_1997_, 5);
v_moreLinkObjs_2005_ = lean_ctor_get(v_cfg_1997_, 6);
v_moreLinkLibs_2006_ = lean_ctor_get(v_cfg_1997_, 7);
v_moreLinkArgs_2007_ = lean_ctor_get(v_cfg_1997_, 8);
v_weakLinkArgs_2008_ = lean_ctor_get(v_cfg_1997_, 9);
v_backend_2009_ = lean_ctor_get_uint8(v_cfg_1997_, sizeof(void*)*13 + 1);
v_platformIndependent_2010_ = lean_ctor_get(v_cfg_1997_, 10);
v_dynlibs_2011_ = lean_ctor_get(v_cfg_1997_, 11);
v_plugins_2012_ = lean_ctor_get(v_cfg_1997_, 12);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_cfg_1997_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2014_ = v_cfg_1997_;
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_plugins_2012_);
lean_inc(v_dynlibs_2011_);
lean_inc(v_platformIndependent_2010_);
lean_inc(v_weakLinkArgs_2008_);
lean_inc(v_moreLinkArgs_2007_);
lean_inc(v_moreLinkLibs_2006_);
lean_inc(v_moreLinkObjs_2005_);
lean_inc(v_weakLeancArgs_2004_);
lean_inc(v_moreServerOptions_2003_);
lean_inc(v_moreLeancArgs_2002_);
lean_inc(v_weakLeanArgs_2001_);
lean_inc(v_moreLeanArgs_2000_);
lean_inc(v_leanOptions_1999_);
lean_dec(v_cfg_1997_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2020_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
v___x_2016_ = lean_apply_1(v_f_1996_, v_plugins_2012_);
if (v_isShared_2015_ == 0)
{
lean_ctor_set(v___x_2014_, 12, v___x_2016_);
v___x_2018_ = v___x_2014_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_leanOptions_1999_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_moreLeanArgs_2000_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_weakLeanArgs_2001_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v_moreLeancArgs_2002_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_moreServerOptions_2003_);
lean_ctor_set(v_reuseFailAlloc_2019_, 5, v_weakLeancArgs_2004_);
lean_ctor_set(v_reuseFailAlloc_2019_, 6, v_moreLinkObjs_2005_);
lean_ctor_set(v_reuseFailAlloc_2019_, 7, v_moreLinkLibs_2006_);
lean_ctor_set(v_reuseFailAlloc_2019_, 8, v_moreLinkArgs_2007_);
lean_ctor_set(v_reuseFailAlloc_2019_, 9, v_weakLinkArgs_2008_);
lean_ctor_set(v_reuseFailAlloc_2019_, 10, v_platformIndependent_2010_);
lean_ctor_set(v_reuseFailAlloc_2019_, 11, v_dynlibs_2011_);
lean_ctor_set(v_reuseFailAlloc_2019_, 12, v___x_2016_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13, v_buildType_1998_);
lean_ctor_set_uint8(v_reuseFailAlloc_2019_, sizeof(void*)*13 + 1, v_backend_2009_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__3(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__2));
v___x_2040_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__0));
v___x_2041_ = lean_array_push(v___x_2040_, v___x_2039_);
return v___x_2041_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__6(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__5));
v___x_2049_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__3, &l_Lake_LeanConfig___fields___closed__3_once, _init_l_Lake_LeanConfig___fields___closed__3);
v___x_2050_ = lean_array_push(v___x_2049_, v___x_2048_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__9(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__8));
v___x_2058_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__6, &l_Lake_LeanConfig___fields___closed__6_once, _init_l_Lake_LeanConfig___fields___closed__6);
v___x_2059_ = lean_array_push(v___x_2058_, v___x_2057_);
return v___x_2059_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__12(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__11));
v___x_2067_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__9, &l_Lake_LeanConfig___fields___closed__9_once, _init_l_Lake_LeanConfig___fields___closed__9);
v___x_2068_ = lean_array_push(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__15(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__14));
v___x_2076_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__12, &l_Lake_LeanConfig___fields___closed__12_once, _init_l_Lake_LeanConfig___fields___closed__12);
v___x_2077_ = lean_array_push(v___x_2076_, v___x_2075_);
return v___x_2077_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__18(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2084_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__17));
v___x_2085_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__15, &l_Lake_LeanConfig___fields___closed__15_once, _init_l_Lake_LeanConfig___fields___closed__15);
v___x_2086_ = lean_array_push(v___x_2085_, v___x_2084_);
return v___x_2086_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__21(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__20));
v___x_2094_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__18, &l_Lake_LeanConfig___fields___closed__18_once, _init_l_Lake_LeanConfig___fields___closed__18);
v___x_2095_ = lean_array_push(v___x_2094_, v___x_2093_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__24(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__23));
v___x_2103_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__21, &l_Lake_LeanConfig___fields___closed__21_once, _init_l_Lake_LeanConfig___fields___closed__21);
v___x_2104_ = lean_array_push(v___x_2103_, v___x_2102_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__27(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__26));
v___x_2112_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__24, &l_Lake_LeanConfig___fields___closed__24_once, _init_l_Lake_LeanConfig___fields___closed__24);
v___x_2113_ = lean_array_push(v___x_2112_, v___x_2111_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__30(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__29));
v___x_2121_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__27, &l_Lake_LeanConfig___fields___closed__27_once, _init_l_Lake_LeanConfig___fields___closed__27);
v___x_2122_ = lean_array_push(v___x_2121_, v___x_2120_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__33(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__32));
v___x_2130_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__30, &l_Lake_LeanConfig___fields___closed__30_once, _init_l_Lake_LeanConfig___fields___closed__30);
v___x_2131_ = lean_array_push(v___x_2130_, v___x_2129_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__36(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v___x_2138_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__35));
v___x_2139_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__33, &l_Lake_LeanConfig___fields___closed__33_once, _init_l_Lake_LeanConfig___fields___closed__33);
v___x_2140_ = lean_array_push(v___x_2139_, v___x_2138_);
return v___x_2140_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__39(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2147_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__38));
v___x_2148_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__36, &l_Lake_LeanConfig___fields___closed__36_once, _init_l_Lake_LeanConfig___fields___closed__36);
v___x_2149_ = lean_array_push(v___x_2148_, v___x_2147_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__42(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__41));
v___x_2157_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__39, &l_Lake_LeanConfig___fields___closed__39_once, _init_l_Lake_LeanConfig___fields___closed__39);
v___x_2158_ = lean_array_push(v___x_2157_, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields___closed__45(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((lean_object*)(l_Lake_LeanConfig___fields___closed__44));
v___x_2166_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__42, &l_Lake_LeanConfig___fields___closed__42_once, _init_l_Lake_LeanConfig___fields___closed__42);
v___x_2167_ = lean_array_push(v___x_2166_, v___x_2165_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lake_LeanConfig___fields(void){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_obj_once(&l_Lake_LeanConfig___fields___closed__45, &l_Lake_LeanConfig___fields___closed__45_once, _init_l_Lake_LeanConfig___fields___closed__45);
return v___x_2168_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigFields(void){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lake_LeanConfig___fields;
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_instConfigInfo___lam__0(lean_object* v_x1_2170_, lean_object* v_x2_2171_){
_start:
{
lean_object* v_name_2172_; lean_object* v___x_2173_; 
v_name_2172_ = lean_ctor_get(v_x2_2171_, 0);
lean_inc(v_name_2172_);
v___x_2173_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_2172_, v_x2_2171_, v_x1_2170_);
return v___x_2173_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__0(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2174_ = l_Lake_LeanConfig___fields;
v___x_2175_ = lean_array_get_size(v___x_2174_);
return v___x_2175_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__11(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_nat_dec_lt(v___x_2196_, v___x_2195_);
return v___x_2197_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__12(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = lean_box(1);
v___x_2200_ = l_Lake_LeanConfig___fields;
v___x_2201_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v___x_2199_);
lean_ctor_set(v___x_2201_, 2, v___x_2198_);
return v___x_2201_;
}
}
static uint8_t _init_l_Lake_LeanConfig_instConfigInfo___closed__14(void){
_start:
{
lean_object* v___x_2203_; uint8_t v___x_2204_; 
v___x_2203_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2204_ = lean_nat_dec_le(v___x_2203_, v___x_2203_);
return v___x_2204_;
}
}
static size_t _init_l_Lake_LeanConfig_instConfigInfo___closed__15(void){
_start:
{
lean_object* v___x_2205_; size_t v___x_2206_; 
v___x_2205_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__0, &l_Lake_LeanConfig_instConfigInfo___closed__0_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__0);
v___x_2206_ = lean_usize_of_nat(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__16(void){
_start:
{
lean_object* v___x_2207_; size_t v___x_2208_; size_t v___x_2209_; lean_object* v___x_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2207_ = lean_box(1);
v___x_2208_ = lean_usize_once(&l_Lake_LeanConfig_instConfigInfo___closed__15, &l_Lake_LeanConfig_instConfigInfo___closed__15_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__15);
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = l_Lake_LeanConfig___fields;
v___f_2211_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__13));
v___x_2212_ = ((lean_object*)(l_Lake_LeanConfig_instConfigInfo___closed__10));
v___x_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2212_, v___f_2211_, v___x_2210_, v___x_2209_, v___x_2208_, v___x_2207_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo___closed__17(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__16, &l_Lake_LeanConfig_instConfigInfo___closed__16_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__16);
v___x_2216_ = l_Lake_LeanConfig___fields;
v___x_2217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
lean_ctor_set(v___x_2217_, 2, v___x_2214_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lake_LeanConfig_instConfigInfo(void){
_start:
{
uint8_t v___x_2218_; 
v___x_2218_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__11, &l_Lake_LeanConfig_instConfigInfo___closed__11_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__11);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2219_;
}
else
{
uint8_t v___x_2220_; 
v___x_2220_ = lean_uint8_once(&l_Lake_LeanConfig_instConfigInfo___closed__14, &l_Lake_LeanConfig_instConfigInfo___closed__14_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__14);
if (v___x_2220_ == 0)
{
if (v___x_2218_ == 0)
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__12, &l_Lake_LeanConfig_instConfigInfo___closed__12_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__12);
return v___x_2221_;
}
else
{
lean_object* v___x_2222_; 
v___x_2222_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2222_;
}
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_obj_once(&l_Lake_LeanConfig_instConfigInfo___closed__17, &l_Lake_LeanConfig_instConfigInfo___closed__17_once, _init_l_Lake_LeanConfig_instConfigInfo___closed__17);
return v___x_2223_;
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

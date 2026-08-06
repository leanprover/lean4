// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.FunDeclInfo
// Imports: public import Lean.Compiler.LCNF.Simp.Basic import Init.Data.Format.Macro
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.Simp.FunDeclInfo.once"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Compiler.LCNF.Simp.FunDeclInfo.many"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__2_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "Lean.Compiler.LCNF.Simp.FunDeclInfo.mustInline"};
static const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__4_value)}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__0_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__2_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx(uint8_t v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(lean_object* v_once_23_){
_start:
{
lean_inc(v_once_23_);
return v_once_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg___boxed(lean_object* v_once_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(v_once_24_);
lean_dec(v_once_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_once_29_){
_start:
{
lean_inc(v_once_29_);
return v_once_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_once_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_once_33_);
lean_dec(v_once_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(lean_object* v_many_36_){
_start:
{
lean_inc(v_many_36_);
return v_many_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg___boxed(lean_object* v_many_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(v_many_37_);
lean_dec(v_many_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_many_42_){
_start:
{
lean_inc(v_many_42_);
return v_many_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_many_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_many_46_);
lean_dec(v_many_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(lean_object* v_mustInline_49_){
_start:
{
lean_inc(v_mustInline_49_);
return v_mustInline_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg___boxed(lean_object* v_mustInline_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(v_mustInline_50_);
lean_dec(v_mustInline_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_mustInline_55_){
_start:
{
lean_inc(v_mustInline_55_);
return v_mustInline_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_mustInline_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_mustInline_59_);
lean_dec(v_mustInline_59_);
return v_res_61_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_to_int(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_unsigned_to_nat(1u);
v___x_74_ = lean_nat_to_int(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(uint8_t v_x_75_, lean_object* v_prec_76_){
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
v___x_100_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_78_ = v___x_100_;
goto v___jp_77_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
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
v___x_104_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_85_ = v___x_104_;
goto v___jp_84_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
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
v___x_108_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_92_ = v___x_108_;
goto v___jp_91_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
v___y_92_ = v___x_109_;
goto v___jp_91_;
}
}
}
v___jp_77_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1));
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
v___x_86_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3));
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
v___x_93_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5));
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___boxed(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
uint8_t v_x_177__boxed_112_; lean_object* v_res_113_; 
v_x_177__boxed_112_ = lean_unbox(v_x_110_);
v_res_113_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v_x_177__boxed_112_, v_prec_111_);
lean_dec(v_prec_111_);
return v_res_113_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default(void){
_start:
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo(void){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_box(0);
v___x_119_ = lean_unsigned_to_nat(16u);
v___x_120_ = lean_mk_array(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_121_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0, &l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default(void){
_start:
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1, &l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default;
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_inc(v_x_126_);
return v_x_126_;
}
else
{
lean_object* v_key_128_; lean_object* v_value_129_; lean_object* v_tail_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v_key_128_ = lean_ctor_get(v_x_127_, 0);
v_value_129_ = lean_ctor_get(v_x_127_, 1);
v_tail_130_ = lean_ctor_get(v_x_127_, 2);
v___x_131_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_x_126_, v_tail_130_);
lean_inc(v_value_129_);
lean_inc(v_key_128_);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v_key_128_);
lean_ctor_set(v___x_132_, 1, v_value_129_);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_131_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0___boxed(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_x_134_, v_x_135_);
lean_dec(v_x_135_);
lean_dec(v_x_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(lean_object* v_as_137_, size_t v_i_138_, size_t v_stop_139_, lean_object* v_b_140_){
_start:
{
uint8_t v___x_141_; 
v___x_141_ = lean_usize_dec_eq(v_i_138_, v_stop_139_);
if (v___x_141_ == 0)
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_sub(v_i_138_, v___x_142_);
v___x_144_ = lean_array_uget_borrowed(v_as_137_, v___x_143_);
v___x_145_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_b_140_, v___x_144_);
lean_dec(v_b_140_);
v_i_138_ = v___x_143_;
v_b_140_ = v___x_145_;
goto _start;
}
else
{
return v_b_140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2___boxed(lean_object* v_as_147_, lean_object* v_i_148_, lean_object* v_stop_149_, lean_object* v_b_150_){
_start:
{
size_t v_i_boxed_151_; size_t v_stop_boxed_152_; lean_object* v_res_153_; 
v_i_boxed_151_ = lean_unbox_usize(v_i_148_);
lean_dec(v_i_148_);
v_stop_boxed_152_ = lean_unbox_usize(v_stop_149_);
lean_dec(v_stop_149_);
v_res_153_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_as_147_, v_i_boxed_151_, v_stop_boxed_152_, v_b_150_);
lean_dec_ref(v_as_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(lean_object* v_as_x27_160_, lean_object* v_b_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
if (lean_obj_tag(v_as_x27_160_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_167_, 0, v_b_161_);
return v___x_167_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v_fst_170_; lean_object* v_snd_171_; lean_object* v___x_172_; 
v_head_168_ = lean_ctor_get(v_as_x27_160_, 0);
v_tail_169_ = lean_ctor_get(v_as_x27_160_, 1);
v_fst_170_ = lean_ctor_get(v_head_168_, 0);
v_snd_171_ = lean_ctor_get(v_head_168_, 1);
lean_inc(v_fst_170_);
v___x_172_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_170_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
lean_inc(v_a_173_);
lean_dec_ref_known(v___x_172_, 1);
v___x_174_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1));
v___x_175_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_175_, 0, v_b_161_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = 1;
v___x_177_ = l_Lean_Name_toString(v_a_173_, v___x_176_);
v___x_178_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
v___x_179_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3));
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_unbox(v_snd_171_);
v___x_183_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v___x_182_, v___x_181_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_180_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_175_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v_as_x27_160_ = v_tail_169_;
v_b_161_ = v___x_185_;
goto _start;
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
lean_dec(v_b_161_);
v_a_187_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_172_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_172_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___boxed(lean_object* v_as_x27_195_, lean_object* v_b_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_195_, v_b_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
lean_dec(v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v_as_x27_195_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object* v_s_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_buckets_209_; lean_object* v_result_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_buckets_209_ = lean_ctor_get(v_s_203_, 1);
v_result_210_ = lean_box(0);
v___x_211_ = lean_box(0);
v___x_212_ = lean_array_get_size(v_buckets_209_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_nat_dec_lt(v___x_213_, v___x_212_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
v___x_215_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_211_, v_result_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
return v___x_215_;
}
else
{
size_t v___x_216_; size_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_216_ = lean_usize_of_nat(v___x_212_);
v___x_217_ = ((size_t)0ULL);
v___x_218_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_buckets_209_, v___x_216_, v___x_217_, v___x_211_);
v___x_219_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_218_, v_result_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v___x_218_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object* v_s_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_s_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec_ref(v_s_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(lean_object* v_as_227_, lean_object* v_as_x27_228_, lean_object* v_b_229_, lean_object* v_a_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_228_, v_b_229_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___boxed(lean_object* v_as_237_, lean_object* v_as_x27_238_, lean_object* v_b_239_, lean_object* v_a_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(v_as_237_, v_as_x27_238_, v_b_239_, v_a_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v_as_x27_238_);
lean_dec(v_as_237_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
return v_x_247_;
}
else
{
lean_object* v_key_249_; lean_object* v_value_250_; lean_object* v_tail_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_274_; 
v_key_249_ = lean_ctor_get(v_x_248_, 0);
v_value_250_ = lean_ctor_get(v_x_248_, 1);
v_tail_251_ = lean_ctor_get(v_x_248_, 2);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_274_ == 0)
{
v___x_253_ = v_x_248_;
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_tail_251_);
lean_inc(v_value_250_);
lean_inc(v_key_249_);
lean_dec(v_x_248_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_274_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v_fold_259_; uint64_t v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_255_ = lean_array_get_size(v_x_247_);
v___x_256_ = l_Lean_instHashableFVarId_hash(v_key_249_);
v___x_257_ = 32ULL;
v___x_258_ = lean_uint64_shift_right(v___x_256_, v___x_257_);
v_fold_259_ = lean_uint64_xor(v___x_256_, v___x_258_);
v___x_260_ = 16ULL;
v___x_261_ = lean_uint64_shift_right(v_fold_259_, v___x_260_);
v___x_262_ = lean_uint64_xor(v_fold_259_, v___x_261_);
v___x_263_ = lean_uint64_to_usize(v___x_262_);
v___x_264_ = lean_usize_of_nat(v___x_255_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_sub(v___x_264_, v___x_265_);
v___x_267_ = lean_usize_land(v___x_263_, v___x_266_);
v___x_268_ = lean_array_uget_borrowed(v_x_247_, v___x_267_);
lean_inc(v___x_268_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 2, v___x_268_);
v___x_270_ = v___x_253_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_key_249_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_value_250_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v___x_268_);
v___x_270_ = v_reuseFailAlloc_273_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_271_; 
v___x_271_ = lean_array_uset(v_x_247_, v___x_267_, v___x_270_);
v_x_247_ = v___x_271_;
v_x_248_ = v_tail_251_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(lean_object* v_i_275_, lean_object* v_source_276_, lean_object* v_target_277_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = lean_array_get_size(v_source_276_);
v___x_279_ = lean_nat_dec_lt(v_i_275_, v___x_278_);
if (v___x_279_ == 0)
{
lean_dec_ref(v_source_276_);
lean_dec(v_i_275_);
return v_target_277_;
}
else
{
lean_object* v_es_280_; lean_object* v___x_281_; lean_object* v_source_282_; lean_object* v_target_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_es_280_ = lean_array_fget(v_source_276_, v_i_275_);
v___x_281_ = lean_box(0);
v_source_282_ = lean_array_fset(v_source_276_, v_i_275_, v___x_281_);
v_target_283_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_target_277_, v_es_280_);
v___x_284_ = lean_unsigned_to_nat(1u);
v___x_285_ = lean_nat_add(v_i_275_, v___x_284_);
lean_dec(v_i_275_);
v_i_275_ = v___x_285_;
v_source_276_ = v_source_282_;
v_target_277_ = v_target_283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(lean_object* v_data_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v_nbuckets_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_288_ = lean_array_get_size(v_data_287_);
v___x_289_ = lean_unsigned_to_nat(2u);
v_nbuckets_290_ = lean_nat_mul(v___x_288_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = lean_box(0);
v___x_293_ = lean_mk_array(v_nbuckets_290_, v___x_292_);
v___x_294_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v___x_291_, v_data_287_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(lean_object* v_a_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
else
{
lean_object* v_key_298_; lean_object* v_tail_299_; uint8_t v___x_300_; 
v_key_298_ = lean_ctor_get(v_x_296_, 0);
v_tail_299_ = lean_ctor_get(v_x_296_, 2);
v___x_300_ = l_Lean_instBEqFVarId_beq(v_key_298_, v_a_295_);
if (v___x_300_ == 0)
{
v_x_296_ = v_tail_299_;
goto _start;
}
else
{
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(lean_object* v_a_302_, lean_object* v_x_303_){
_start:
{
uint8_t v_res_304_; lean_object* v_r_305_; 
v_res_304_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_302_, v_x_303_);
lean_dec(v_x_303_);
lean_dec(v_a_302_);
v_r_305_ = lean_box(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(lean_object* v_a_306_, lean_object* v_b_307_, lean_object* v_x_308_){
_start:
{
if (lean_obj_tag(v_x_308_) == 0)
{
lean_dec(v_b_307_);
lean_dec(v_a_306_);
return v_x_308_;
}
else
{
lean_object* v_key_309_; lean_object* v_value_310_; lean_object* v_tail_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_323_; 
v_key_309_ = lean_ctor_get(v_x_308_, 0);
v_value_310_ = lean_ctor_get(v_x_308_, 1);
v_tail_311_ = lean_ctor_get(v_x_308_, 2);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_308_);
if (v_isSharedCheck_323_ == 0)
{
v___x_313_ = v_x_308_;
v_isShared_314_ = v_isSharedCheck_323_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_tail_311_);
lean_inc(v_value_310_);
lean_inc(v_key_309_);
lean_dec(v_x_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_323_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint8_t v___x_315_; 
v___x_315_ = l_Lean_instBEqFVarId_beq(v_key_309_, v_a_306_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_318_; 
v___x_316_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_306_, v_b_307_, v_tail_311_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 2, v___x_316_);
v___x_318_ = v___x_313_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_key_309_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_value_310_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v___x_321_; 
lean_dec(v_value_310_);
lean_dec(v_key_309_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_b_307_);
lean_ctor_set(v___x_313_, 0, v_a_306_);
v___x_321_ = v___x_313_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_306_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_b_307_);
lean_ctor_set(v_reuseFailAlloc_322_, 2, v_tail_311_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(lean_object* v_m_324_, lean_object* v_a_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_size_327_; lean_object* v_buckets_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_371_; 
v_size_327_ = lean_ctor_get(v_m_324_, 0);
v_buckets_328_ = lean_ctor_get(v_m_324_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_m_324_);
if (v_isSharedCheck_371_ == 0)
{
v___x_330_ = v_m_324_;
v_isShared_331_ = v_isSharedCheck_371_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_buckets_328_);
lean_inc(v_size_327_);
lean_dec(v_m_324_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_371_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v_fold_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v_bkt_345_; uint8_t v___x_346_; 
v___x_332_ = lean_array_get_size(v_buckets_328_);
v___x_333_ = l_Lean_instHashableFVarId_hash(v_a_325_);
v___x_334_ = 32ULL;
v___x_335_ = lean_uint64_shift_right(v___x_333_, v___x_334_);
v_fold_336_ = lean_uint64_xor(v___x_333_, v___x_335_);
v___x_337_ = 16ULL;
v___x_338_ = lean_uint64_shift_right(v_fold_336_, v___x_337_);
v___x_339_ = lean_uint64_xor(v_fold_336_, v___x_338_);
v___x_340_ = lean_uint64_to_usize(v___x_339_);
v___x_341_ = lean_usize_of_nat(v___x_332_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v___x_341_, v___x_342_);
v___x_344_ = lean_usize_land(v___x_340_, v___x_343_);
v_bkt_345_ = lean_array_uget_borrowed(v_buckets_328_, v___x_344_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_325_, v_bkt_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v_size_x27_348_; lean_object* v___x_349_; lean_object* v_buckets_x27_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v_size_x27_348_ = lean_nat_add(v_size_327_, v___x_347_);
lean_dec(v_size_327_);
lean_inc(v_bkt_345_);
v___x_349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_349_, 0, v_a_325_);
lean_ctor_set(v___x_349_, 1, v_b_326_);
lean_ctor_set(v___x_349_, 2, v_bkt_345_);
v_buckets_x27_350_ = lean_array_uset(v_buckets_328_, v___x_344_, v___x_349_);
v___x_351_ = lean_unsigned_to_nat(4u);
v___x_352_ = lean_nat_mul(v_size_x27_348_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(3u);
v___x_354_ = lean_nat_div(v___x_352_, v___x_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_array_get_size(v_buckets_x27_350_);
v___x_356_ = lean_nat_dec_le(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
if (v___x_356_ == 0)
{
lean_object* v_val_357_; lean_object* v___x_359_; 
v_val_357_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_buckets_x27_350_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_val_357_);
lean_ctor_set(v___x_330_, 0, v_size_x27_348_);
v___x_359_ = v___x_330_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_size_x27_348_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_val_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
else
{
lean_object* v___x_362_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_buckets_x27_350_);
lean_ctor_set(v___x_330_, 0, v_size_x27_348_);
v___x_362_ = v___x_330_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_size_x27_348_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_buckets_x27_350_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
else
{
lean_object* v___x_364_; lean_object* v_buckets_x27_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
lean_inc(v_bkt_345_);
v___x_364_ = lean_box(0);
v_buckets_x27_365_ = lean_array_uset(v_buckets_328_, v___x_344_, v___x_364_);
v___x_366_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_325_, v_b_326_, v_bkt_345_);
v___x_367_ = lean_array_uset(v_buckets_x27_365_, v___x_344_, v___x_366_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v___x_367_);
v___x_369_ = v___x_330_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_size_327_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(lean_object* v_a_372_, lean_object* v_x_373_){
_start:
{
if (lean_obj_tag(v_x_373_) == 0)
{
lean_object* v___x_374_; 
v___x_374_ = lean_box(0);
return v___x_374_;
}
else
{
lean_object* v_key_375_; lean_object* v_value_376_; lean_object* v_tail_377_; uint8_t v___x_378_; 
v_key_375_ = lean_ctor_get(v_x_373_, 0);
v_value_376_ = lean_ctor_get(v_x_373_, 1);
v_tail_377_ = lean_ctor_get(v_x_373_, 2);
v___x_378_ = l_Lean_instBEqFVarId_beq(v_key_375_, v_a_372_);
if (v___x_378_ == 0)
{
v_x_373_ = v_tail_377_;
goto _start;
}
else
{
lean_object* v___x_380_; 
lean_inc(v_value_376_);
v___x_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_380_, 0, v_value_376_);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_381_, lean_object* v_x_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_381_, v_x_382_);
lean_dec(v_x_382_);
lean_dec(v_a_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(lean_object* v_m_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_buckets_386_; lean_object* v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v_fold_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_buckets_386_ = lean_ctor_get(v_m_384_, 1);
v___x_387_ = lean_array_get_size(v_buckets_386_);
v___x_388_ = l_Lean_instHashableFVarId_hash(v_a_385_);
v___x_389_ = 32ULL;
v___x_390_ = lean_uint64_shift_right(v___x_388_, v___x_389_);
v_fold_391_ = lean_uint64_xor(v___x_388_, v___x_390_);
v___x_392_ = 16ULL;
v___x_393_ = lean_uint64_shift_right(v_fold_391_, v___x_392_);
v___x_394_ = lean_uint64_xor(v_fold_391_, v___x_393_);
v___x_395_ = lean_uint64_to_usize(v___x_394_);
v___x_396_ = lean_usize_of_nat(v___x_387_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_sub(v___x_396_, v___x_397_);
v___x_399_ = lean_usize_land(v___x_395_, v___x_398_);
v___x_400_ = lean_array_uget_borrowed(v_buckets_386_, v___x_399_);
v___x_401_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_385_, v___x_400_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg___boxed(lean_object* v_m_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_m_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object* v_s_405_, lean_object* v_fvarId_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_405_, v_fvarId_406_);
if (lean_obj_tag(v___x_407_) == 0)
{
uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_408_ = 0;
v___x_409_ = lean_box(v___x_408_);
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_405_, v_fvarId_406_, v___x_409_);
return v___x_410_;
}
else
{
lean_object* v_val_411_; uint8_t v___x_412_; 
v_val_411_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_411_);
lean_dec_ref_known(v___x_407_, 1);
v___x_412_ = lean_unbox(v_val_411_);
lean_dec(v_val_411_);
if (v___x_412_ == 0)
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = 1;
v___x_414_ = lean_box(v___x_413_);
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_405_, v_fvarId_406_, v___x_414_);
return v___x_415_;
}
else
{
lean_dec(v_fvarId_406_);
return v_s_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(lean_object* v_00_u03b2_416_, lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_417_, v_a_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(v_00_u03b2_420_, v_m_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec_ref(v_m_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(lean_object* v_00_u03b2_424_, lean_object* v_m_425_, lean_object* v_a_426_, lean_object* v_b_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_425_, v_a_426_, v_b_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(lean_object* v_00_u03b2_429_, lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_430_, v_x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_433_, lean_object* v_a_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(v_00_u03b2_433_, v_a_434_, v_x_435_);
lean_dec(v_x_435_);
lean_dec(v_a_434_);
return v_res_436_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_object* v_00_u03b2_437_, lean_object* v_a_438_, lean_object* v_x_439_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_438_, v_x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(lean_object* v_00_u03b2_441_, lean_object* v_a_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(v_00_u03b2_441_, v_a_442_, v_x_443_);
lean_dec(v_x_443_);
lean_dec(v_a_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3(lean_object* v_00_u03b2_446_, lean_object* v_data_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_data_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4(lean_object* v_00_u03b2_449_, lean_object* v_a_450_, lean_object* v_b_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_450_, v_b_451_, v_x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_454_, lean_object* v_i_455_, lean_object* v_source_456_, lean_object* v_target_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v_i_455_, v_source_456_, v_target_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_x_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object* v_s_463_, lean_object* v_fvarId_464_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_463_, v_fvarId_464_);
if (lean_obj_tag(v___x_469_) == 0)
{
goto v___jp_465_;
}
else
{
lean_object* v_val_470_; uint8_t v___x_471_; 
v_val_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_val_470_);
lean_dec_ref_known(v___x_469_, 1);
v___x_471_ = lean_unbox(v_val_470_);
lean_dec(v_val_470_);
if (v___x_471_ == 0)
{
goto v___jp_465_;
}
else
{
lean_dec(v_fvarId_464_);
return v_s_463_;
}
}
v___jp_465_:
{
uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_466_ = 1;
v___x_467_ = lean_box(v___x_466_);
v___x_468_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_463_, v_fvarId_464_, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object* v_s_472_, lean_object* v_fvarId_473_){
_start:
{
uint8_t v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_474_ = 2;
v___x_475_ = lean_box(v___x_474_);
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_472_, v_fvarId_473_, v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(lean_object* v_a_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
return v_x_478_;
}
else
{
lean_object* v_key_479_; lean_object* v_value_480_; lean_object* v_tail_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_490_; 
v_key_479_ = lean_ctor_get(v_x_478_, 0);
v_value_480_ = lean_ctor_get(v_x_478_, 1);
v_tail_481_ = lean_ctor_get(v_x_478_, 2);
v_isSharedCheck_490_ = !lean_is_exclusive(v_x_478_);
if (v_isSharedCheck_490_ == 0)
{
v___x_483_ = v_x_478_;
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_tail_481_);
lean_inc(v_value_480_);
lean_inc(v_key_479_);
lean_dec(v_x_478_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_490_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
uint8_t v___x_485_; 
v___x_485_ = l_Lean_instBEqFVarId_beq(v_key_479_, v_a_477_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_488_; 
v___x_486_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_477_, v_tail_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 2, v___x_486_);
v___x_488_ = v___x_483_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_key_479_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_value_480_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v___x_486_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
else
{
lean_del_object(v___x_483_);
lean_dec(v_value_480_);
lean_dec(v_key_479_);
return v_tail_481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg___boxed(lean_object* v_a_491_, lean_object* v_x_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_491_, v_x_492_);
lean_dec(v_a_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_size_496_; lean_object* v_buckets_497_; lean_object* v___x_498_; uint64_t v___x_499_; uint64_t v___x_500_; uint64_t v___x_501_; uint64_t v_fold_502_; uint64_t v___x_503_; uint64_t v___x_504_; uint64_t v___x_505_; size_t v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v_bkt_511_; uint8_t v___x_512_; 
v_size_496_ = lean_ctor_get(v_m_494_, 0);
v_buckets_497_ = lean_ctor_get(v_m_494_, 1);
v___x_498_ = lean_array_get_size(v_buckets_497_);
v___x_499_ = l_Lean_instHashableFVarId_hash(v_a_495_);
v___x_500_ = 32ULL;
v___x_501_ = lean_uint64_shift_right(v___x_499_, v___x_500_);
v_fold_502_ = lean_uint64_xor(v___x_499_, v___x_501_);
v___x_503_ = 16ULL;
v___x_504_ = lean_uint64_shift_right(v_fold_502_, v___x_503_);
v___x_505_ = lean_uint64_xor(v_fold_502_, v___x_504_);
v___x_506_ = lean_uint64_to_usize(v___x_505_);
v___x_507_ = lean_usize_of_nat(v___x_498_);
v___x_508_ = ((size_t)1ULL);
v___x_509_ = lean_usize_sub(v___x_507_, v___x_508_);
v___x_510_ = lean_usize_land(v___x_506_, v___x_509_);
v_bkt_511_ = lean_array_uget_borrowed(v_buckets_497_, v___x_510_);
v___x_512_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_495_, v_bkt_511_);
if (v___x_512_ == 0)
{
return v_m_494_;
}
else
{
lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_525_; 
lean_inc(v_bkt_511_);
lean_inc_ref(v_buckets_497_);
lean_inc(v_size_496_);
v_isSharedCheck_525_ = !lean_is_exclusive(v_m_494_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; lean_object* v_unused_527_; 
v_unused_526_ = lean_ctor_get(v_m_494_, 1);
lean_dec(v_unused_526_);
v_unused_527_ = lean_ctor_get(v_m_494_, 0);
lean_dec(v_unused_527_);
v___x_514_ = v_m_494_;
v_isShared_515_ = v_isSharedCheck_525_;
goto v_resetjp_513_;
}
else
{
lean_dec(v_m_494_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_525_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v_buckets_x27_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_516_ = lean_box(0);
v_buckets_x27_517_ = lean_array_uset(v_buckets_497_, v___x_510_, v___x_516_);
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_sub(v_size_496_, v___x_518_);
lean_dec(v_size_496_);
v___x_520_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_495_, v_bkt_511_);
v___x_521_ = lean_array_uset(v_buckets_x27_517_, v___x_510_, v___x_520_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v___x_521_);
lean_ctor_set(v___x_514_, 0, v___x_519_);
v___x_523_ = v___x_514_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_519_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(lean_object* v_m_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_528_, v_a_529_);
lean_dec(v_a_529_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object* v_s_531_, lean_object* v_fvarId_532_, lean_object* v_saved_x3f_533_){
_start:
{
if (lean_obj_tag(v_saved_x3f_533_) == 0)
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_s_531_, v_fvarId_532_);
lean_dec(v_fvarId_532_);
return v___x_534_;
}
else
{
lean_object* v_val_535_; lean_object* v___x_536_; 
v_val_535_ = lean_ctor_get(v_saved_x3f_533_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v_saved_x3f_533_, 1);
v___x_536_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_531_, v_fvarId_532_, v_val_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(lean_object* v_00_u03b2_537_, lean_object* v_m_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_538_, v_a_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(lean_object* v_00_u03b2_541_, lean_object* v_m_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(v_00_u03b2_541_, v_m_542_, v_a_543_);
lean_dec(v_a_543_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(lean_object* v_00_u03b2_545_, lean_object* v_a_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_546_, v_x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_549_, lean_object* v_a_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(v_00_u03b2_549_, v_a_550_, v_x_551_);
lean_dec(v_a_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(lean_object* v_arg_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
if (lean_obj_tag(v_arg_553_) == 1)
{
lean_object* v_fvarId_557_; uint8_t v___x_558_; lean_object* v___x_559_; 
v_fvarId_557_ = lean_ctor_get(v_arg_553_, 0);
lean_inc(v_fvarId_557_);
lean_dec_ref_known(v_arg_553_, 1);
v___x_558_ = 0;
v___x_559_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_558_, v_fvarId_557_, v_a_555_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_577_; 
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_577_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_577_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_577_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
if (lean_obj_tag(v_a_560_) == 1)
{
lean_object* v_val_564_; lean_object* v___x_565_; lean_object* v_fvarId_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v_val_564_ = lean_ctor_get(v_a_560_, 0);
lean_inc(v_val_564_);
lean_dec_ref_known(v_a_560_, 1);
v___x_565_ = lean_st_ref_take(v_a_554_);
v_fvarId_566_ = lean_ctor_get(v_val_564_, 0);
lean_inc(v_fvarId_566_);
lean_dec(v_val_564_);
v___x_567_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v___x_565_, v_fvarId_566_);
v___x_568_ = lean_st_ref_set(v_a_554_, v___x_567_);
v___x_569_ = lean_box(0);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_569_);
v___x_571_ = v___x_562_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_575_; 
lean_dec(v_a_560_);
v___x_573_ = lean_box(0);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_573_);
v___x_575_ = v___x_562_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
v_a_578_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_559_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_559_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_arg_553_);
v___x_586_ = lean_box(0);
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg___boxed(lean_object* v_arg_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_588_, v_a_589_, v_a_590_);
lean_dec(v_a_590_);
lean_dec(v_a_589_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(lean_object* v_arg_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_593_, v_a_594_, v_a_596_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___boxed(lean_object* v_arg_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(v_arg_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(lean_object* v_as_609_, size_t v_i_610_, size_t v_stop_611_, lean_object* v_b_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_eq(v_i_610_, v_stop_611_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_array_uget_borrowed(v_as_609_, v_i_610_);
lean_inc(v___x_617_);
v___x_618_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v___x_617_, v___y_613_, v___y_614_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v_a_619_; size_t v___x_620_; size_t v___x_621_; 
v_a_619_ = lean_ctor_get(v___x_618_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v___x_618_, 1);
v___x_620_ = ((size_t)1ULL);
v___x_621_ = lean_usize_add(v_i_610_, v___x_620_);
v_i_610_ = v___x_621_;
v_b_612_ = v_a_619_;
goto _start;
}
else
{
return v___x_618_;
}
}
else
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v_b_612_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg___boxed(lean_object* v_as_624_, lean_object* v_i_625_, lean_object* v_stop_626_, lean_object* v_b_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
size_t v_i_boxed_631_; size_t v_stop_boxed_632_; lean_object* v_res_633_; 
v_i_boxed_631_ = lean_unbox_usize(v_i_625_);
lean_dec(v_i_625_);
v_stop_boxed_632_ = lean_unbox_usize(v_stop_626_);
lean_dec(v_stop_626_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_624_, v_i_boxed_631_, v_stop_boxed_632_, v_b_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v_as_624_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(lean_object* v_e_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_){
_start:
{
switch(lean_obj_tag(v_e_634_))
{
case 0:
{
lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_648_; 
v_isSharedCheck_648_ = !lean_is_exclusive(v_e_634_);
if (v_isSharedCheck_648_ == 0)
{
lean_object* v_unused_649_; 
v_unused_649_ = lean_ctor_get(v_e_634_, 0);
lean_dec(v_unused_649_);
v___x_642_ = v_e_634_;
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
else
{
lean_dec(v_e_634_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_648_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_644_ = lean_box(0);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_644_);
v___x_646_ = v___x_642_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
case 3:
{
lean_object* v_args_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_args_650_ = lean_ctor_get(v_e_634_, 2);
lean_inc_ref(v_args_650_);
lean_dec_ref_known(v_e_634_, 3);
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_args_650_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v_args_650_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_653_);
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = lean_nat_dec_le(v___x_652_, v___x_652_);
if (v___x_656_ == 0)
{
if (v___x_654_ == 0)
{
lean_object* v___x_657_; 
lean_dec_ref(v_args_650_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v___x_653_);
return v___x_657_;
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_652_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_650_, v___x_658_, v___x_659_, v___x_653_, v_a_635_, v_a_637_);
lean_dec_ref(v_args_650_);
return v___x_660_;
}
}
else
{
size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_652_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_650_, v___x_661_, v___x_662_, v___x_653_, v_a_635_, v_a_637_);
lean_dec_ref(v_args_650_);
return v___x_663_;
}
}
}
case 4:
{
lean_object* v_fvarId_664_; lean_object* v_args_665_; uint8_t v___x_666_; lean_object* v___x_667_; 
v_fvarId_664_ = lean_ctor_get(v_e_634_, 0);
lean_inc(v_fvarId_664_);
v_args_665_ = lean_ctor_get(v_e_634_, 1);
lean_inc_ref(v_args_665_);
lean_dec_ref_known(v_e_634_, 2);
v___x_666_ = 0;
v___x_667_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_666_, v_fvarId_664_, v_a_637_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_698_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_698_ == 0)
{
v___x_670_ = v___x_667_;
v_isShared_671_ = v_isSharedCheck_698_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_a_668_);
lean_dec(v___x_667_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_698_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
if (lean_obj_tag(v_a_668_) == 1)
{
lean_object* v_val_672_; lean_object* v___x_673_; lean_object* v_fvarId_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_val_672_ = lean_ctor_get(v_a_668_, 0);
lean_inc(v_val_672_);
lean_dec_ref_known(v_a_668_, 1);
v___x_673_ = lean_st_ref_take(v_a_635_);
v_fvarId_674_ = lean_ctor_get(v_val_672_, 0);
lean_inc(v_fvarId_674_);
lean_dec(v_val_672_);
v___x_675_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_673_, v_fvarId_674_);
v___x_676_ = lean_st_ref_set(v_a_635_, v___x_675_);
v___x_677_ = lean_unsigned_to_nat(0u);
v___x_678_ = lean_array_get_size(v_args_665_);
v___x_679_ = lean_box(0);
v___x_680_ = lean_nat_dec_lt(v___x_677_, v___x_678_);
if (v___x_680_ == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v_args_665_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_679_);
v___x_682_ = v___x_670_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_679_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
else
{
uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_le(v___x_678_, v___x_678_);
if (v___x_684_ == 0)
{
if (v___x_680_ == 0)
{
lean_object* v___x_686_; 
lean_dec_ref(v_args_665_);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_679_);
v___x_686_ = v___x_670_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_679_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
else
{
size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
lean_del_object(v___x_670_);
v___x_688_ = ((size_t)0ULL);
v___x_689_ = lean_usize_of_nat(v___x_678_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_665_, v___x_688_, v___x_689_, v___x_679_, v_a_635_, v_a_637_);
lean_dec_ref(v_args_665_);
return v___x_690_;
}
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
lean_del_object(v___x_670_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_678_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_665_, v___x_691_, v___x_692_, v___x_679_, v_a_635_, v_a_637_);
lean_dec_ref(v_args_665_);
return v___x_693_;
}
}
}
else
{
lean_object* v___x_694_; lean_object* v___x_696_; 
lean_dec(v_a_668_);
lean_dec_ref(v_args_665_);
v___x_694_ = lean_box(0);
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 0, v___x_694_);
v___x_696_ = v___x_670_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_args_665_);
v_a_699_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_667_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_667_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
default: 
{
lean_object* v___x_707_; lean_object* v___x_708_; 
lean_dec(v_e_634_);
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_708_, 0, v___x_707_);
return v___x_708_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs___boxed(lean_object* v_e_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_e_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(lean_object* v_as_717_, size_t v_i_718_, size_t v_stop_719_, lean_object* v_b_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_717_, v_i_718_, v_stop_719_, v_b_720_, v___y_721_, v___y_723_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___boxed(lean_object* v_as_728_, lean_object* v_i_729_, lean_object* v_stop_730_, lean_object* v_b_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
size_t v_i_boxed_738_; size_t v_stop_boxed_739_; lean_object* v_res_740_; 
v_i_boxed_738_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_stop_boxed_739_ = lean_unbox_usize(v_stop_730_);
lean_dec(v_stop_730_);
v_res_740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(v_as_728_, v_i_boxed_738_, v_stop_boxed_739_, v_b_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v_as_728_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(uint8_t v_mustInline_741_, lean_object* v_code_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_){
_start:
{
switch(lean_obj_tag(v_code_742_))
{
case 0:
{
lean_object* v_decl_749_; lean_object* v_k_750_; lean_object* v_value_751_; lean_object* v___x_752_; 
v_decl_749_ = lean_ctor_get(v_code_742_, 0);
lean_inc_ref(v_decl_749_);
v_k_750_ = lean_ctor_get(v_code_742_, 1);
lean_inc_ref(v_k_750_);
lean_dec_ref_known(v_code_742_, 2);
v_value_751_ = lean_ctor_get(v_decl_749_, 3);
lean_inc(v_value_751_);
lean_dec_ref(v_decl_749_);
v___x_752_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_value_751_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_dec_ref_known(v___x_752_, 1);
v_code_742_ = v_k_750_;
goto _start;
}
else
{
lean_dec_ref(v_k_750_);
return v___x_752_;
}
}
case 1:
{
lean_object* v_decl_754_; lean_object* v_k_755_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; 
v_decl_754_ = lean_ctor_get(v_code_742_, 0);
lean_inc_ref(v_decl_754_);
v_k_755_ = lean_ctor_get(v_code_742_, 1);
lean_inc_ref(v_k_755_);
lean_dec_ref_known(v_code_742_, 2);
if (v_mustInline_741_ == 0)
{
v___y_757_ = v_a_743_;
v___y_758_ = v_a_744_;
v___y_759_ = v_a_745_;
v___y_760_ = v_a_746_;
v___y_761_ = v_a_747_;
goto v___jp_756_;
}
else
{
lean_object* v___x_765_; lean_object* v_fvarId_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_765_ = lean_st_ref_take(v_a_743_);
v_fvarId_766_ = lean_ctor_get(v_decl_754_, 0);
lean_inc(v_fvarId_766_);
v___x_767_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v___x_765_, v_fvarId_766_);
v___x_768_ = lean_st_ref_set(v_a_743_, v___x_767_);
v___y_757_ = v_a_743_;
v___y_758_ = v_a_744_;
v___y_759_ = v_a_745_;
v___y_760_ = v_a_746_;
v___y_761_ = v_a_747_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v_value_762_; lean_object* v___x_763_; 
v_value_762_ = lean_ctor_get(v_decl_754_, 4);
lean_inc_ref(v_value_762_);
lean_dec_ref(v_decl_754_);
v___x_763_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_741_, v_value_762_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_dec_ref_known(v___x_763_, 1);
v_code_742_ = v_k_755_;
v_a_743_ = v___y_757_;
v_a_744_ = v___y_758_;
v_a_745_ = v___y_759_;
v_a_746_ = v___y_760_;
v_a_747_ = v___y_761_;
goto _start;
}
else
{
lean_dec_ref(v_k_755_);
return v___x_763_;
}
}
}
case 2:
{
lean_object* v_decl_769_; lean_object* v_k_770_; lean_object* v_value_771_; lean_object* v___x_772_; 
v_decl_769_ = lean_ctor_get(v_code_742_, 0);
lean_inc_ref(v_decl_769_);
v_k_770_ = lean_ctor_get(v_code_742_, 1);
lean_inc_ref(v_k_770_);
lean_dec_ref_known(v_code_742_, 2);
v_value_771_ = lean_ctor_get(v_decl_769_, 4);
lean_inc_ref(v_value_771_);
lean_dec_ref(v_decl_769_);
v___x_772_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_741_, v_value_771_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_dec_ref_known(v___x_772_, 1);
v_code_742_ = v_k_770_;
goto _start;
}
else
{
lean_dec_ref(v_k_770_);
return v___x_772_;
}
}
case 3:
{
lean_object* v_fvarId_774_; lean_object* v_args_775_; uint8_t v___x_776_; lean_object* v___x_777_; 
v_fvarId_774_ = lean_ctor_get(v_code_742_, 0);
lean_inc(v_fvarId_774_);
v_args_775_ = lean_ctor_get(v_code_742_, 1);
lean_inc_ref(v_args_775_);
lean_dec_ref_known(v_code_742_, 2);
v___x_776_ = 0;
v___x_777_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_776_, v_fvarId_774_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_803_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_803_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_803_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_803_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_782_; lean_object* v_fvarId_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_782_ = lean_st_ref_take(v_a_743_);
v_fvarId_783_ = lean_ctor_get(v_a_778_, 0);
lean_inc(v_fvarId_783_);
lean_dec(v_a_778_);
v___x_784_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_782_, v_fvarId_783_);
v___x_785_ = lean_st_ref_set(v_a_743_, v___x_784_);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_array_get_size(v_args_775_);
v___x_788_ = lean_box(0);
v___x_789_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_791_; 
lean_dec_ref(v_args_775_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_788_);
v___x_791_ = v___x_780_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
uint8_t v___x_793_; 
v___x_793_ = lean_nat_dec_le(v___x_787_, v___x_787_);
if (v___x_793_ == 0)
{
if (v___x_789_ == 0)
{
lean_object* v___x_795_; 
lean_dec_ref(v_args_775_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_788_);
v___x_795_ = v___x_780_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_788_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
else
{
size_t v___x_797_; size_t v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_780_);
v___x_797_ = ((size_t)0ULL);
v___x_798_ = lean_usize_of_nat(v___x_787_);
v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_775_, v___x_797_, v___x_798_, v___x_788_, v_a_743_, v_a_745_);
lean_dec_ref(v_args_775_);
return v___x_799_;
}
}
else
{
size_t v___x_800_; size_t v___x_801_; lean_object* v___x_802_; 
lean_del_object(v___x_780_);
v___x_800_ = ((size_t)0ULL);
v___x_801_ = lean_usize_of_nat(v___x_787_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_775_, v___x_800_, v___x_801_, v___x_788_, v_a_743_, v_a_745_);
lean_dec_ref(v_args_775_);
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref(v_args_775_);
v_a_804_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_777_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_777_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
case 4:
{
lean_object* v_cases_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_834_; 
v_cases_812_ = lean_ctor_get(v_code_742_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_code_742_);
if (v_isSharedCheck_834_ == 0)
{
v___x_814_ = v_code_742_;
v_isShared_815_ = v_isSharedCheck_834_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_cases_812_);
lean_dec(v_code_742_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_834_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_alts_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_alts_816_ = lean_ctor_get(v_cases_812_, 3);
lean_inc_ref(v_alts_816_);
lean_dec_ref(v_cases_812_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_array_get_size(v_alts_816_);
v___x_819_ = lean_box(0);
v___x_820_ = lean_nat_dec_lt(v___x_817_, v___x_818_);
if (v___x_820_ == 0)
{
lean_object* v___x_822_; 
lean_dec_ref(v_alts_816_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_819_);
v___x_822_ = v___x_814_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_819_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_le(v___x_818_, v___x_818_);
if (v___x_824_ == 0)
{
if (v___x_820_ == 0)
{
lean_object* v___x_826_; 
lean_dec_ref(v_alts_816_);
if (v_isShared_815_ == 0)
{
lean_ctor_set_tag(v___x_814_, 0);
lean_ctor_set(v___x_814_, 0, v___x_819_);
v___x_826_ = v___x_814_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_819_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
else
{
size_t v___x_828_; size_t v___x_829_; lean_object* v___x_830_; 
lean_del_object(v___x_814_);
v___x_828_ = ((size_t)0ULL);
v___x_829_ = lean_usize_of_nat(v___x_818_);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_741_, v_alts_816_, v___x_828_, v___x_829_, v___x_819_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec_ref(v_alts_816_);
return v___x_830_;
}
}
else
{
size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; 
lean_del_object(v___x_814_);
v___x_831_ = ((size_t)0ULL);
v___x_832_ = lean_usize_of_nat(v___x_818_);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_741_, v_alts_816_, v___x_831_, v___x_832_, v___x_819_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_);
lean_dec_ref(v_alts_816_);
return v___x_833_;
}
}
}
}
default: 
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v_code_742_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v_code_742_, 0);
lean_dec(v_unused_843_);
v___x_836_ = v_code_742_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_dec(v_code_742_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_840_; 
v___x_838_ = lean_box(0);
if (v_isShared_837_ == 0)
{
lean_ctor_set_tag(v___x_836_, 0);
lean_ctor_set(v___x_836_, 0, v___x_838_);
v___x_840_ = v___x_836_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(uint8_t v_mustInline_844_, lean_object* v_as_845_, size_t v_i_846_, size_t v_stop_847_, lean_object* v_b_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___y_856_; uint8_t v___x_862_; 
v___x_862_ = lean_usize_dec_eq(v_i_846_, v_stop_847_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
v___x_863_ = lean_array_uget_borrowed(v_as_845_, v_i_846_);
switch(lean_obj_tag(v___x_863_))
{
case 0:
{
lean_object* v_code_864_; 
v_code_864_ = lean_ctor_get(v___x_863_, 2);
lean_inc_ref(v_code_864_);
v___y_856_ = v_code_864_;
goto v___jp_855_;
}
case 1:
{
lean_object* v_code_865_; 
v_code_865_ = lean_ctor_get(v___x_863_, 1);
lean_inc_ref(v_code_865_);
v___y_856_ = v_code_865_;
goto v___jp_855_;
}
default: 
{
lean_object* v_code_866_; 
v_code_866_ = lean_ctor_get(v___x_863_, 0);
lean_inc_ref(v_code_866_);
v___y_856_ = v_code_866_;
goto v___jp_855_;
}
}
}
else
{
lean_object* v___x_867_; 
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v_b_848_);
return v___x_867_;
}
v___jp_855_:
{
lean_object* v___x_857_; 
v___x_857_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_844_, v___y_856_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; size_t v___x_859_; size_t v___x_860_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_add(v_i_846_, v___x_859_);
v_i_846_ = v___x_860_;
v_b_848_ = v_a_858_;
goto _start;
}
else
{
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0___boxed(lean_object* v_mustInline_868_, lean_object* v_as_869_, lean_object* v_i_870_, lean_object* v_stop_871_, lean_object* v_b_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v_mustInline_boxed_879_; size_t v_i_boxed_880_; size_t v_stop_boxed_881_; lean_object* v_res_882_; 
v_mustInline_boxed_879_ = lean_unbox(v_mustInline_868_);
v_i_boxed_880_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_stop_boxed_881_ = lean_unbox_usize(v_stop_871_);
lean_dec(v_stop_871_);
v_res_882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_boxed_879_, v_as_869_, v_i_boxed_880_, v_stop_boxed_881_, v_b_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v_as_869_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go___boxed(lean_object* v_mustInline_883_, lean_object* v_code_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
uint8_t v_mustInline_boxed_891_; lean_object* v_res_892_; 
v_mustInline_boxed_891_ = lean_unbox(v_mustInline_883_);
v_res_892_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_boxed_891_, v_code_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object* v_s_893_, lean_object* v_code_894_, uint8_t v_mustInline_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_st_mk_ref(v_s_893_);
v___x_902_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_895_, v_code_894_, v___x_901_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_910_; 
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_910_ == 0)
{
lean_object* v_unused_911_; 
v_unused_911_ = lean_ctor_get(v___x_902_, 0);
lean_dec(v_unused_911_);
v___x_904_ = v___x_902_;
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
else
{
lean_dec(v___x_902_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_910_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = lean_st_ref_get(v___x_901_);
lean_dec(v___x_901_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v___x_901_);
v_a_912_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_902_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_902_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update___boxed(lean_object* v_s_920_, lean_object* v_code_921_, lean_object* v_mustInline_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
uint8_t v_mustInline_boxed_928_; lean_object* v_res_929_; 
v_mustInline_boxed_928_ = lean_unbox(v_mustInline_922_);
v_res_929_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_s_920_, v_code_921_, v_mustInline_boxed_928_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_929_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default();
l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo();
l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default);
l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap = _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
}
#ifdef __cplusplus
}
#endif

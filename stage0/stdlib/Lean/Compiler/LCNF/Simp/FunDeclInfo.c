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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(lean_object* v_once_28_){
_start:
{
lean_inc(v_once_28_);
return v_once_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg___boxed(lean_object* v_once_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(v_once_29_);
lean_dec(v_once_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_once_34_){
_start:
{
lean_inc(v_once_34_);
return v_once_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_once_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_once_38_);
lean_dec(v_once_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(lean_object* v_many_41_){
_start:
{
lean_inc(v_many_41_);
return v_many_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg___boxed(lean_object* v_many_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(v_many_42_);
lean_dec(v_many_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_many_47_){
_start:
{
lean_inc(v_many_47_);
return v_many_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_many_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_many_51_);
lean_dec(v_many_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(lean_object* v_mustInline_54_){
_start:
{
lean_inc(v_mustInline_54_);
return v_mustInline_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg___boxed(lean_object* v_mustInline_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(v_mustInline_55_);
lean_dec(v_mustInline_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_mustInline_60_){
_start:
{
lean_inc(v_mustInline_60_);
return v_mustInline_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_mustInline_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_mustInline_64_);
lean_dec(v_mustInline_64_);
return v_res_66_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(2u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_to_int(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(uint8_t v_x_80_, lean_object* v_prec_81_){
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
v___x_105_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_83_ = v___x_105_;
goto v___jp_82_;
}
else
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
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
v___x_109_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_90_ = v___x_109_;
goto v___jp_89_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
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
v___x_113_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_97_ = v___x_113_;
goto v___jp_96_;
}
else
{
lean_object* v___x_114_; 
v___x_114_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
v___y_97_ = v___x_114_;
goto v___jp_96_;
}
}
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_84_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1));
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
v___x_91_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3));
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
v___x_98_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5));
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_177__boxed_117_; lean_object* v_res_118_; 
v_x_177__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v_x_177__boxed_117_, v_prec_116_);
lean_dec(v_prec_116_);
return v_res_118_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo_default(void){
_start:
{
uint8_t v___x_121_; 
v___x_121_ = 0;
return v___x_121_;
}
}
static uint8_t _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfo(void){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = 0;
return v___x_122_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_unsigned_to_nat(16u);
v___x_125_ = lean_mk_array(v___x_124_, v___x_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_126_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0, &l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0);
v___x_127_ = lean_unsigned_to_nat(0u);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
return v___x_128_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1, &l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap(void){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default;
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 0)
{
lean_inc(v_x_131_);
return v_x_131_;
}
else
{
lean_object* v_key_133_; lean_object* v_value_134_; lean_object* v_tail_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_key_133_ = lean_ctor_get(v_x_132_, 0);
v_value_134_ = lean_ctor_get(v_x_132_, 1);
v_tail_135_ = lean_ctor_get(v_x_132_, 2);
v___x_136_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_x_131_, v_tail_135_);
lean_inc(v_value_134_);
lean_inc(v_key_133_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_key_133_);
lean_ctor_set(v___x_137_, 1, v_value_134_);
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0___boxed(lean_object* v_x_139_, lean_object* v_x_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_x_139_, v_x_140_);
lean_dec(v_x_140_);
lean_dec(v_x_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(lean_object* v_as_142_, size_t v_i_143_, size_t v_stop_144_, lean_object* v_b_145_){
_start:
{
uint8_t v___x_146_; 
v___x_146_ = lean_usize_dec_eq(v_i_143_, v_stop_144_);
if (v___x_146_ == 0)
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v_i_143_, v___x_147_);
v___x_149_ = lean_array_uget_borrowed(v_as_142_, v___x_148_);
v___x_150_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_b_145_, v___x_149_);
lean_dec(v_b_145_);
v_i_143_ = v___x_148_;
v_b_145_ = v___x_150_;
goto _start;
}
else
{
return v_b_145_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2___boxed(lean_object* v_as_152_, lean_object* v_i_153_, lean_object* v_stop_154_, lean_object* v_b_155_){
_start:
{
size_t v_i_boxed_156_; size_t v_stop_boxed_157_; lean_object* v_res_158_; 
v_i_boxed_156_ = lean_unbox_usize(v_i_153_);
lean_dec(v_i_153_);
v_stop_boxed_157_ = lean_unbox_usize(v_stop_154_);
lean_dec(v_stop_154_);
v_res_158_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_as_152_, v_i_boxed_156_, v_stop_boxed_157_, v_b_155_);
lean_dec_ref(v_as_152_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(lean_object* v_as_x27_165_, lean_object* v_b_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
if (lean_obj_tag(v_as_x27_165_) == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v_b_166_);
return v___x_172_;
}
else
{
lean_object* v_head_173_; lean_object* v_tail_174_; lean_object* v_fst_175_; lean_object* v_snd_176_; lean_object* v___x_177_; 
v_head_173_ = lean_ctor_get(v_as_x27_165_, 0);
v_tail_174_ = lean_ctor_get(v_as_x27_165_, 1);
v_fst_175_ = lean_ctor_get(v_head_173_, 0);
v_snd_176_ = lean_ctor_get(v_head_173_, 1);
lean_inc(v_fst_175_);
v___x_177_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_175_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
if (lean_obj_tag(v___x_177_) == 0)
{
lean_object* v_a_178_; lean_object* v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_a_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc(v_a_178_);
lean_dec_ref(v___x_177_);
v___x_179_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1));
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v_b_166_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = 1;
v___x_182_ = l_Lean_Name_toString(v_a_178_, v___x_181_);
v___x_183_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
v___x_184_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3));
v___x_185_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_185_, 0, v___x_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_unbox(v_snd_176_);
v___x_188_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v___x_187_, v___x_186_);
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_185_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_180_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v_as_x27_165_ = v_tail_174_;
v_b_166_ = v___x_190_;
goto _start;
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v_b_166_);
v_a_192_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_177_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_177_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___boxed(lean_object* v_as_x27_200_, lean_object* v_b_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_200_, v_b_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v_as_x27_200_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object* v_s_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_buckets_214_; lean_object* v_result_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_buckets_214_ = lean_ctor_get(v_s_208_, 1);
v_result_215_ = lean_box(0);
v___x_216_ = lean_box(0);
v___x_217_ = lean_array_get_size(v_buckets_214_);
v___x_218_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_nat_dec_lt(v___x_218_, v___x_217_);
if (v___x_219_ == 0)
{
lean_object* v___x_220_; 
v___x_220_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_216_, v_result_215_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
return v___x_220_;
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_221_ = lean_usize_of_nat(v___x_217_);
v___x_222_ = ((size_t)0ULL);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_buckets_214_, v___x_221_, v___x_222_, v___x_216_);
v___x_224_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_223_, v_result_215_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v___x_223_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object* v_s_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_s_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec_ref(v_s_225_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(lean_object* v_as_232_, lean_object* v_as_x27_233_, lean_object* v_b_234_, lean_object* v_a_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_233_, v_b_234_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___boxed(lean_object* v_as_242_, lean_object* v_as_x27_243_, lean_object* v_b_244_, lean_object* v_a_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(v_as_242_, v_as_x27_243_, v_b_244_, v_a_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v_as_x27_243_);
lean_dec(v_as_242_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_252_, lean_object* v_x_253_){
_start:
{
if (lean_obj_tag(v_x_253_) == 0)
{
return v_x_252_;
}
else
{
lean_object* v_key_254_; lean_object* v_value_255_; lean_object* v_tail_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_279_; 
v_key_254_ = lean_ctor_get(v_x_253_, 0);
v_value_255_ = lean_ctor_get(v_x_253_, 1);
v_tail_256_ = lean_ctor_get(v_x_253_, 2);
v_isSharedCheck_279_ = !lean_is_exclusive(v_x_253_);
if (v_isSharedCheck_279_ == 0)
{
v___x_258_ = v_x_253_;
v_isShared_259_ = v_isSharedCheck_279_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_tail_256_);
lean_inc(v_value_255_);
lean_inc(v_key_254_);
lean_dec(v_x_253_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_279_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; uint64_t v___x_263_; uint64_t v_fold_264_; uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_260_ = lean_array_get_size(v_x_252_);
v___x_261_ = l_Lean_instHashableFVarId_hash(v_key_254_);
v___x_262_ = 32ULL;
v___x_263_ = lean_uint64_shift_right(v___x_261_, v___x_262_);
v_fold_264_ = lean_uint64_xor(v___x_261_, v___x_263_);
v___x_265_ = 16ULL;
v___x_266_ = lean_uint64_shift_right(v_fold_264_, v___x_265_);
v___x_267_ = lean_uint64_xor(v_fold_264_, v___x_266_);
v___x_268_ = lean_uint64_to_usize(v___x_267_);
v___x_269_ = lean_usize_of_nat(v___x_260_);
v___x_270_ = ((size_t)1ULL);
v___x_271_ = lean_usize_sub(v___x_269_, v___x_270_);
v___x_272_ = lean_usize_land(v___x_268_, v___x_271_);
v___x_273_ = lean_array_uget_borrowed(v_x_252_, v___x_272_);
lean_inc(v___x_273_);
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 2, v___x_273_);
v___x_275_ = v___x_258_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_key_254_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_value_255_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v___x_273_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; 
v___x_276_ = lean_array_uset(v_x_252_, v___x_272_, v___x_275_);
v_x_252_ = v___x_276_;
v_x_253_ = v_tail_256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(lean_object* v_i_280_, lean_object* v_source_281_, lean_object* v_target_282_){
_start:
{
lean_object* v___x_283_; uint8_t v___x_284_; 
v___x_283_ = lean_array_get_size(v_source_281_);
v___x_284_ = lean_nat_dec_lt(v_i_280_, v___x_283_);
if (v___x_284_ == 0)
{
lean_dec_ref(v_source_281_);
lean_dec(v_i_280_);
return v_target_282_;
}
else
{
lean_object* v_es_285_; lean_object* v___x_286_; lean_object* v_source_287_; lean_object* v_target_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_es_285_ = lean_array_fget(v_source_281_, v_i_280_);
v___x_286_ = lean_box(0);
v_source_287_ = lean_array_fset(v_source_281_, v_i_280_, v___x_286_);
v_target_288_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_target_282_, v_es_285_);
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_i_280_, v___x_289_);
lean_dec(v_i_280_);
v_i_280_ = v___x_290_;
v_source_281_ = v_source_287_;
v_target_282_ = v_target_288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(lean_object* v_data_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_nbuckets_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_293_ = lean_array_get_size(v_data_292_);
v___x_294_ = lean_unsigned_to_nat(2u);
v_nbuckets_295_ = lean_nat_mul(v___x_293_, v___x_294_);
v___x_296_ = lean_unsigned_to_nat(0u);
v___x_297_ = lean_box(0);
v___x_298_ = lean_mk_array(v_nbuckets_295_, v___x_297_);
v___x_299_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v___x_296_, v_data_292_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(lean_object* v_a_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
else
{
lean_object* v_key_303_; lean_object* v_tail_304_; uint8_t v___x_305_; 
v_key_303_ = lean_ctor_get(v_x_301_, 0);
v_tail_304_ = lean_ctor_get(v_x_301_, 2);
v___x_305_ = l_Lean_instBEqFVarId_beq(v_key_303_, v_a_300_);
if (v___x_305_ == 0)
{
v_x_301_ = v_tail_304_;
goto _start;
}
else
{
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(lean_object* v_a_307_, lean_object* v_x_308_){
_start:
{
uint8_t v_res_309_; lean_object* v_r_310_; 
v_res_309_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_307_, v_x_308_);
lean_dec(v_x_308_);
lean_dec(v_a_307_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(lean_object* v_a_311_, lean_object* v_b_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_dec(v_b_312_);
lean_dec(v_a_311_);
return v_x_313_;
}
else
{
lean_object* v_key_314_; lean_object* v_value_315_; lean_object* v_tail_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_328_; 
v_key_314_ = lean_ctor_get(v_x_313_, 0);
v_value_315_ = lean_ctor_get(v_x_313_, 1);
v_tail_316_ = lean_ctor_get(v_x_313_, 2);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_328_ == 0)
{
v___x_318_ = v_x_313_;
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_tail_316_);
lean_inc(v_value_315_);
lean_inc(v_key_314_);
lean_dec(v_x_313_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_328_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = l_Lean_instBEqFVarId_beq(v_key_314_, v_a_311_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_311_, v_b_312_, v_tail_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 2, v___x_321_);
v___x_323_ = v___x_318_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_key_314_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_value_315_);
lean_ctor_set(v_reuseFailAlloc_324_, 2, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec(v_value_315_);
lean_dec(v_key_314_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v_b_312_);
lean_ctor_set(v___x_318_, 0, v_a_311_);
v___x_326_ = v___x_318_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_b_312_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_tail_316_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(lean_object* v_m_329_, lean_object* v_a_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_size_332_; lean_object* v_buckets_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_376_; 
v_size_332_ = lean_ctor_get(v_m_329_, 0);
v_buckets_333_ = lean_ctor_get(v_m_329_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_m_329_);
if (v_isSharedCheck_376_ == 0)
{
v___x_335_ = v_m_329_;
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_buckets_333_);
lean_inc(v_size_332_);
lean_dec(v_m_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_376_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v___x_340_; uint64_t v_fold_341_; uint64_t v___x_342_; uint64_t v___x_343_; uint64_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v_bkt_350_; uint8_t v___x_351_; 
v___x_337_ = lean_array_get_size(v_buckets_333_);
v___x_338_ = l_Lean_instHashableFVarId_hash(v_a_330_);
v___x_339_ = 32ULL;
v___x_340_ = lean_uint64_shift_right(v___x_338_, v___x_339_);
v_fold_341_ = lean_uint64_xor(v___x_338_, v___x_340_);
v___x_342_ = 16ULL;
v___x_343_ = lean_uint64_shift_right(v_fold_341_, v___x_342_);
v___x_344_ = lean_uint64_xor(v_fold_341_, v___x_343_);
v___x_345_ = lean_uint64_to_usize(v___x_344_);
v___x_346_ = lean_usize_of_nat(v___x_337_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_sub(v___x_346_, v___x_347_);
v___x_349_ = lean_usize_land(v___x_345_, v___x_348_);
v_bkt_350_ = lean_array_uget_borrowed(v_buckets_333_, v___x_349_);
v___x_351_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_330_, v_bkt_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; lean_object* v_size_x27_353_; lean_object* v___x_354_; lean_object* v_buckets_x27_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v_size_x27_353_ = lean_nat_add(v_size_332_, v___x_352_);
lean_dec(v_size_332_);
lean_inc(v_bkt_350_);
v___x_354_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_354_, 0, v_a_330_);
lean_ctor_set(v___x_354_, 1, v_b_331_);
lean_ctor_set(v___x_354_, 2, v_bkt_350_);
v_buckets_x27_355_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_354_);
v___x_356_ = lean_unsigned_to_nat(4u);
v___x_357_ = lean_nat_mul(v_size_x27_353_, v___x_356_);
v___x_358_ = lean_unsigned_to_nat(3u);
v___x_359_ = lean_nat_div(v___x_357_, v___x_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_array_get_size(v_buckets_x27_355_);
v___x_361_ = lean_nat_dec_le(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
if (v___x_361_ == 0)
{
lean_object* v_val_362_; lean_object* v___x_364_; 
v_val_362_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_buckets_x27_355_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_val_362_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_364_ = v___x_335_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_val_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
else
{
lean_object* v___x_367_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v_buckets_x27_355_);
lean_ctor_set(v___x_335_, 0, v_size_x27_353_);
v___x_367_ = v___x_335_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_size_x27_353_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v_buckets_x27_355_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
else
{
lean_object* v___x_369_; lean_object* v_buckets_x27_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_inc(v_bkt_350_);
v___x_369_ = lean_box(0);
v_buckets_x27_370_ = lean_array_uset(v_buckets_333_, v___x_349_, v___x_369_);
v___x_371_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_330_, v_b_331_, v_bkt_350_);
v___x_372_ = lean_array_uset(v_buckets_x27_370_, v___x_349_, v___x_371_);
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 1, v___x_372_);
v___x_374_ = v___x_335_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_size_332_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(lean_object* v_a_377_, lean_object* v_x_378_){
_start:
{
if (lean_obj_tag(v_x_378_) == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_box(0);
return v___x_379_;
}
else
{
lean_object* v_key_380_; lean_object* v_value_381_; lean_object* v_tail_382_; uint8_t v___x_383_; 
v_key_380_ = lean_ctor_get(v_x_378_, 0);
v_value_381_ = lean_ctor_get(v_x_378_, 1);
v_tail_382_ = lean_ctor_get(v_x_378_, 2);
v___x_383_ = l_Lean_instBEqFVarId_beq(v_key_380_, v_a_377_);
if (v___x_383_ == 0)
{
v_x_378_ = v_tail_382_;
goto _start;
}
else
{
lean_object* v___x_385_; 
lean_inc(v_value_381_);
v___x_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_385_, 0, v_value_381_);
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_386_, v_x_387_);
lean_dec(v_x_387_);
lean_dec(v_a_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(lean_object* v_m_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_buckets_391_; lean_object* v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; uint64_t v_fold_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_buckets_391_ = lean_ctor_get(v_m_389_, 1);
v___x_392_ = lean_array_get_size(v_buckets_391_);
v___x_393_ = l_Lean_instHashableFVarId_hash(v_a_390_);
v___x_394_ = 32ULL;
v___x_395_ = lean_uint64_shift_right(v___x_393_, v___x_394_);
v_fold_396_ = lean_uint64_xor(v___x_393_, v___x_395_);
v___x_397_ = 16ULL;
v___x_398_ = lean_uint64_shift_right(v_fold_396_, v___x_397_);
v___x_399_ = lean_uint64_xor(v_fold_396_, v___x_398_);
v___x_400_ = lean_uint64_to_usize(v___x_399_);
v___x_401_ = lean_usize_of_nat(v___x_392_);
v___x_402_ = ((size_t)1ULL);
v___x_403_ = lean_usize_sub(v___x_401_, v___x_402_);
v___x_404_ = lean_usize_land(v___x_400_, v___x_403_);
v___x_405_ = lean_array_uget_borrowed(v_buckets_391_, v___x_404_);
v___x_406_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_390_, v___x_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg___boxed(lean_object* v_m_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_m_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object* v_s_410_, lean_object* v_fvarId_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_410_, v_fvarId_411_);
if (lean_obj_tag(v___x_412_) == 0)
{
uint8_t v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = 0;
v___x_414_ = lean_box(v___x_413_);
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_410_, v_fvarId_411_, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v_val_416_; uint8_t v___x_417_; 
v_val_416_ = lean_ctor_get(v___x_412_, 0);
lean_inc(v_val_416_);
lean_dec_ref(v___x_412_);
v___x_417_ = lean_unbox(v_val_416_);
lean_dec(v_val_416_);
if (v___x_417_ == 0)
{
uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = 1;
v___x_419_ = lean_box(v___x_418_);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_410_, v_fvarId_411_, v___x_419_);
return v___x_420_;
}
else
{
lean_dec(v_fvarId_411_);
return v_s_410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(lean_object* v_00_u03b2_421_, lean_object* v_m_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_422_, v_a_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(lean_object* v_00_u03b2_425_, lean_object* v_m_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(v_00_u03b2_425_, v_m_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_m_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(lean_object* v_00_u03b2_429_, lean_object* v_m_430_, lean_object* v_a_431_, lean_object* v_b_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_430_, v_a_431_, v_b_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(lean_object* v_00_u03b2_434_, lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_435_, v_x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_438_, lean_object* v_a_439_, lean_object* v_x_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(v_00_u03b2_438_, v_a_439_, v_x_440_);
lean_dec(v_x_440_);
lean_dec(v_a_439_);
return v_res_441_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_object* v_00_u03b2_442_, lean_object* v_a_443_, lean_object* v_x_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_443_, v_x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(v_00_u03b2_446_, v_a_447_, v_x_448_);
lean_dec(v_x_448_);
lean_dec(v_a_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3(lean_object* v_00_u03b2_451_, lean_object* v_data_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_data_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4(lean_object* v_00_u03b2_454_, lean_object* v_a_455_, lean_object* v_b_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_455_, v_b_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_459_, lean_object* v_i_460_, lean_object* v_source_461_, lean_object* v_target_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v_i_460_, v_source_461_, v_target_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_x_465_, v_x_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object* v_s_468_, lean_object* v_fvarId_469_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_468_, v_fvarId_469_);
if (lean_obj_tag(v___x_474_) == 0)
{
goto v___jp_470_;
}
else
{
lean_object* v_val_475_; uint8_t v___x_476_; 
v_val_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_val_475_);
lean_dec_ref(v___x_474_);
v___x_476_ = lean_unbox(v_val_475_);
lean_dec(v_val_475_);
if (v___x_476_ == 0)
{
goto v___jp_470_;
}
else
{
lean_dec(v_fvarId_469_);
return v_s_468_;
}
}
v___jp_470_:
{
uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = 1;
v___x_472_ = lean_box(v___x_471_);
v___x_473_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_468_, v_fvarId_469_, v___x_472_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object* v_s_477_, lean_object* v_fvarId_478_){
_start:
{
uint8_t v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = 2;
v___x_480_ = lean_box(v___x_479_);
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_477_, v_fvarId_478_, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(lean_object* v_a_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
return v_x_483_;
}
else
{
lean_object* v_key_484_; lean_object* v_value_485_; lean_object* v_tail_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_495_; 
v_key_484_ = lean_ctor_get(v_x_483_, 0);
v_value_485_ = lean_ctor_get(v_x_483_, 1);
v_tail_486_ = lean_ctor_get(v_x_483_, 2);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_495_ == 0)
{
v___x_488_ = v_x_483_;
v_isShared_489_ = v_isSharedCheck_495_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_tail_486_);
lean_inc(v_value_485_);
lean_inc(v_key_484_);
lean_dec(v_x_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_495_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
uint8_t v___x_490_; 
v___x_490_ = l_Lean_instBEqFVarId_beq(v_key_484_, v_a_482_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_491_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_482_, v_tail_486_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v___x_491_);
v___x_493_ = v___x_488_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_key_484_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_value_485_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
lean_del_object(v___x_488_);
lean_dec(v_value_485_);
lean_dec(v_key_484_);
return v_tail_486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg___boxed(lean_object* v_a_496_, lean_object* v_x_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_496_, v_x_497_);
lean_dec(v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(lean_object* v_m_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_size_501_; lean_object* v_buckets_502_; lean_object* v___x_503_; uint64_t v___x_504_; uint64_t v___x_505_; uint64_t v___x_506_; uint64_t v_fold_507_; uint64_t v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; size_t v___x_511_; size_t v___x_512_; size_t v___x_513_; size_t v___x_514_; size_t v___x_515_; lean_object* v_bkt_516_; uint8_t v___x_517_; 
v_size_501_ = lean_ctor_get(v_m_499_, 0);
v_buckets_502_ = lean_ctor_get(v_m_499_, 1);
v___x_503_ = lean_array_get_size(v_buckets_502_);
v___x_504_ = l_Lean_instHashableFVarId_hash(v_a_500_);
v___x_505_ = 32ULL;
v___x_506_ = lean_uint64_shift_right(v___x_504_, v___x_505_);
v_fold_507_ = lean_uint64_xor(v___x_504_, v___x_506_);
v___x_508_ = 16ULL;
v___x_509_ = lean_uint64_shift_right(v_fold_507_, v___x_508_);
v___x_510_ = lean_uint64_xor(v_fold_507_, v___x_509_);
v___x_511_ = lean_uint64_to_usize(v___x_510_);
v___x_512_ = lean_usize_of_nat(v___x_503_);
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_sub(v___x_512_, v___x_513_);
v___x_515_ = lean_usize_land(v___x_511_, v___x_514_);
v_bkt_516_ = lean_array_uget_borrowed(v_buckets_502_, v___x_515_);
v___x_517_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_500_, v_bkt_516_);
if (v___x_517_ == 0)
{
return v_m_499_;
}
else
{
lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_530_; 
lean_inc(v_bkt_516_);
lean_inc_ref(v_buckets_502_);
lean_inc(v_size_501_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_m_499_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; lean_object* v_unused_532_; 
v_unused_531_ = lean_ctor_get(v_m_499_, 1);
lean_dec(v_unused_531_);
v_unused_532_ = lean_ctor_get(v_m_499_, 0);
lean_dec(v_unused_532_);
v___x_519_ = v_m_499_;
v_isShared_520_ = v_isSharedCheck_530_;
goto v_resetjp_518_;
}
else
{
lean_dec(v_m_499_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_530_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_521_; lean_object* v_buckets_x27_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_521_ = lean_box(0);
v_buckets_x27_522_ = lean_array_uset(v_buckets_502_, v___x_515_, v___x_521_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_sub(v_size_501_, v___x_523_);
lean_dec(v_size_501_);
v___x_525_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_500_, v_bkt_516_);
v___x_526_ = lean_array_uset(v_buckets_x27_522_, v___x_515_, v___x_525_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 1, v___x_526_);
lean_ctor_set(v___x_519_, 0, v___x_524_);
v___x_528_ = v___x_519_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(lean_object* v_m_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_533_, v_a_534_);
lean_dec(v_a_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object* v_s_536_, lean_object* v_fvarId_537_, lean_object* v_saved_x3f_538_){
_start:
{
if (lean_obj_tag(v_saved_x3f_538_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_s_536_, v_fvarId_537_);
lean_dec(v_fvarId_537_);
return v___x_539_;
}
else
{
lean_object* v_val_540_; lean_object* v___x_541_; 
v_val_540_ = lean_ctor_get(v_saved_x3f_538_, 0);
lean_inc(v_val_540_);
lean_dec_ref(v_saved_x3f_538_);
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_536_, v_fvarId_537_, v_val_540_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(lean_object* v_00_u03b2_542_, lean_object* v_m_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_543_, v_a_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(lean_object* v_00_u03b2_546_, lean_object* v_m_547_, lean_object* v_a_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(v_00_u03b2_546_, v_m_547_, v_a_548_);
lean_dec(v_a_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(lean_object* v_00_u03b2_550_, lean_object* v_a_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_551_, v_x_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_554_, lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(v_00_u03b2_554_, v_a_555_, v_x_556_);
lean_dec(v_a_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(lean_object* v_arg_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
if (lean_obj_tag(v_arg_558_) == 1)
{
lean_object* v_fvarId_562_; uint8_t v___x_563_; lean_object* v___x_564_; 
v_fvarId_562_ = lean_ctor_get(v_arg_558_, 0);
lean_inc(v_fvarId_562_);
lean_dec_ref(v_arg_558_);
v___x_563_ = 0;
v___x_564_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_563_, v_fvarId_562_, v_a_560_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_582_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_582_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_582_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_582_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
if (lean_obj_tag(v_a_565_) == 1)
{
lean_object* v_val_569_; lean_object* v___x_570_; lean_object* v_fvarId_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v_val_569_ = lean_ctor_get(v_a_565_, 0);
lean_inc(v_val_569_);
lean_dec_ref(v_a_565_);
v___x_570_ = lean_st_ref_take(v_a_559_);
v_fvarId_571_ = lean_ctor_get(v_val_569_, 0);
lean_inc(v_fvarId_571_);
lean_dec(v_val_569_);
v___x_572_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v___x_570_, v_fvarId_571_);
v___x_573_ = lean_st_ref_set(v_a_559_, v___x_572_);
v___x_574_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_574_);
v___x_576_ = v___x_567_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_580_; 
lean_dec(v_a_565_);
v___x_578_ = lean_box(0);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_578_);
v___x_580_ = v___x_567_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
v_a_583_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_564_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_564_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v_arg_558_);
v___x_591_ = lean_box(0);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg___boxed(lean_object* v_arg_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_593_, v_a_594_, v_a_595_);
lean_dec(v_a_595_);
lean_dec(v_a_594_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(lean_object* v_arg_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_598_, v_a_599_, v_a_601_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___boxed(lean_object* v_arg_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(v_arg_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(lean_object* v_as_614_, size_t v_i_615_, size_t v_stop_616_, lean_object* v_b_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_eq(v_i_615_, v_stop_616_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_array_uget_borrowed(v_as_614_, v_i_615_);
lean_inc(v___x_622_);
v___x_623_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v___x_622_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; size_t v___x_625_; size_t v___x_626_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_624_);
lean_dec_ref(v___x_623_);
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_615_, v___x_625_);
v_i_615_ = v___x_626_;
v_b_617_ = v_a_624_;
goto _start;
}
else
{
return v___x_623_;
}
}
else
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v_b_617_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg___boxed(lean_object* v_as_629_, lean_object* v_i_630_, lean_object* v_stop_631_, lean_object* v_b_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
size_t v_i_boxed_636_; size_t v_stop_boxed_637_; lean_object* v_res_638_; 
v_i_boxed_636_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_stop_boxed_637_ = lean_unbox_usize(v_stop_631_);
lean_dec(v_stop_631_);
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_629_, v_i_boxed_636_, v_stop_boxed_637_, v_b_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v_as_629_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(lean_object* v_e_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
switch(lean_obj_tag(v_e_639_))
{
case 0:
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v_isSharedCheck_653_ = !lean_is_exclusive(v_e_639_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_e_639_, 0);
lean_dec(v_unused_654_);
v___x_647_ = v_e_639_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_dec(v_e_639_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_box(0);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
case 3:
{
lean_object* v_args_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_args_655_ = lean_ctor_get(v_e_639_, 2);
lean_inc_ref(v_args_655_);
lean_dec_ref(v_e_639_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_args_655_);
v___x_658_ = lean_box(0);
v___x_659_ = lean_nat_dec_lt(v___x_656_, v___x_657_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; 
lean_dec_ref(v_args_655_);
v___x_660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
return v___x_660_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = lean_nat_dec_le(v___x_657_, v___x_657_);
if (v___x_661_ == 0)
{
if (v___x_659_ == 0)
{
lean_object* v___x_662_; 
lean_dec_ref(v_args_655_);
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___x_658_);
return v___x_662_;
}
else
{
size_t v___x_663_; size_t v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((size_t)0ULL);
v___x_664_ = lean_usize_of_nat(v___x_657_);
v___x_665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_655_, v___x_663_, v___x_664_, v___x_658_, v_a_640_, v_a_642_);
lean_dec_ref(v_args_655_);
return v___x_665_;
}
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_657_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_655_, v___x_666_, v___x_667_, v___x_658_, v_a_640_, v_a_642_);
lean_dec_ref(v_args_655_);
return v___x_668_;
}
}
}
case 4:
{
lean_object* v_fvarId_669_; lean_object* v_args_670_; uint8_t v___x_671_; lean_object* v___x_672_; 
v_fvarId_669_ = lean_ctor_get(v_e_639_, 0);
lean_inc(v_fvarId_669_);
v_args_670_ = lean_ctor_get(v_e_639_, 1);
lean_inc_ref(v_args_670_);
lean_dec_ref(v_e_639_);
v___x_671_ = 0;
v___x_672_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_671_, v_fvarId_669_, v_a_642_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_703_; 
v_a_673_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_703_ == 0)
{
v___x_675_ = v___x_672_;
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_703_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
if (lean_obj_tag(v_a_673_) == 1)
{
lean_object* v_val_677_; lean_object* v___x_678_; lean_object* v_fvarId_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
v_val_677_ = lean_ctor_get(v_a_673_, 0);
lean_inc(v_val_677_);
lean_dec_ref(v_a_673_);
v___x_678_ = lean_st_ref_take(v_a_640_);
v_fvarId_679_ = lean_ctor_get(v_val_677_, 0);
lean_inc(v_fvarId_679_);
lean_dec(v_val_677_);
v___x_680_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_678_, v_fvarId_679_);
v___x_681_ = lean_st_ref_set(v_a_640_, v___x_680_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_array_get_size(v_args_670_);
v___x_684_ = lean_box(0);
v___x_685_ = lean_nat_dec_lt(v___x_682_, v___x_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_687_; 
lean_dec_ref(v_args_670_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_684_);
v___x_687_ = v___x_675_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v___x_684_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
else
{
uint8_t v___x_689_; 
v___x_689_ = lean_nat_dec_le(v___x_683_, v___x_683_);
if (v___x_689_ == 0)
{
if (v___x_685_ == 0)
{
lean_object* v___x_691_; 
lean_dec_ref(v_args_670_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_684_);
v___x_691_ = v___x_675_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_684_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
else
{
size_t v___x_693_; size_t v___x_694_; lean_object* v___x_695_; 
lean_del_object(v___x_675_);
v___x_693_ = ((size_t)0ULL);
v___x_694_ = lean_usize_of_nat(v___x_683_);
v___x_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_670_, v___x_693_, v___x_694_, v___x_684_, v_a_640_, v_a_642_);
lean_dec_ref(v_args_670_);
return v___x_695_;
}
}
else
{
size_t v___x_696_; size_t v___x_697_; lean_object* v___x_698_; 
lean_del_object(v___x_675_);
v___x_696_ = ((size_t)0ULL);
v___x_697_ = lean_usize_of_nat(v___x_683_);
v___x_698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_670_, v___x_696_, v___x_697_, v___x_684_, v_a_640_, v_a_642_);
lean_dec_ref(v_args_670_);
return v___x_698_;
}
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_701_; 
lean_dec(v_a_673_);
lean_dec_ref(v_args_670_);
v___x_699_ = lean_box(0);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 0, v___x_699_);
v___x_701_ = v___x_675_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec_ref(v_args_670_);
v_a_704_ = lean_ctor_get(v___x_672_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_672_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_672_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
default: 
{
lean_object* v___x_712_; lean_object* v___x_713_; 
lean_dec(v_e_639_);
v___x_712_ = lean_box(0);
v___x_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs___boxed(lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_e_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(lean_object* v_as_722_, size_t v_i_723_, size_t v_stop_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_722_, v_i_723_, v_stop_724_, v_b_725_, v___y_726_, v___y_728_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___boxed(lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_stop_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
size_t v_i_boxed_743_; size_t v_stop_boxed_744_; lean_object* v_res_745_; 
v_i_boxed_743_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_stop_boxed_744_ = lean_unbox_usize(v_stop_735_);
lean_dec(v_stop_735_);
v_res_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(v_as_733_, v_i_boxed_743_, v_stop_boxed_744_, v_b_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_);
lean_dec(v___y_741_);
lean_dec_ref(v___y_740_);
lean_dec(v___y_739_);
lean_dec_ref(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v_as_733_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(uint8_t v_mustInline_746_, lean_object* v_code_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
switch(lean_obj_tag(v_code_747_))
{
case 0:
{
lean_object* v_decl_754_; lean_object* v_k_755_; lean_object* v_value_756_; lean_object* v___x_757_; 
v_decl_754_ = lean_ctor_get(v_code_747_, 0);
lean_inc_ref(v_decl_754_);
v_k_755_ = lean_ctor_get(v_code_747_, 1);
lean_inc_ref(v_k_755_);
lean_dec_ref(v_code_747_);
v_value_756_ = lean_ctor_get(v_decl_754_, 3);
lean_inc(v_value_756_);
lean_dec_ref(v_decl_754_);
v___x_757_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_value_756_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref(v___x_757_);
v_code_747_ = v_k_755_;
goto _start;
}
else
{
lean_dec_ref(v_k_755_);
return v___x_757_;
}
}
case 1:
{
lean_object* v_decl_759_; lean_object* v_k_760_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; 
v_decl_759_ = lean_ctor_get(v_code_747_, 0);
lean_inc_ref(v_decl_759_);
v_k_760_ = lean_ctor_get(v_code_747_, 1);
lean_inc_ref(v_k_760_);
lean_dec_ref(v_code_747_);
if (v_mustInline_746_ == 0)
{
v___y_762_ = v_a_748_;
v___y_763_ = v_a_749_;
v___y_764_ = v_a_750_;
v___y_765_ = v_a_751_;
v___y_766_ = v_a_752_;
goto v___jp_761_;
}
else
{
lean_object* v___x_770_; lean_object* v_fvarId_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_770_ = lean_st_ref_take(v_a_748_);
v_fvarId_771_ = lean_ctor_get(v_decl_759_, 0);
lean_inc(v_fvarId_771_);
v___x_772_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v___x_770_, v_fvarId_771_);
v___x_773_ = lean_st_ref_set(v_a_748_, v___x_772_);
v___y_762_ = v_a_748_;
v___y_763_ = v_a_749_;
v___y_764_ = v_a_750_;
v___y_765_ = v_a_751_;
v___y_766_ = v_a_752_;
goto v___jp_761_;
}
v___jp_761_:
{
lean_object* v_value_767_; lean_object* v___x_768_; 
v_value_767_ = lean_ctor_get(v_decl_759_, 4);
lean_inc_ref(v_value_767_);
lean_dec_ref(v_decl_759_);
v___x_768_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_746_, v_value_767_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_dec_ref(v___x_768_);
v_code_747_ = v_k_760_;
v_a_748_ = v___y_762_;
v_a_749_ = v___y_763_;
v_a_750_ = v___y_764_;
v_a_751_ = v___y_765_;
v_a_752_ = v___y_766_;
goto _start;
}
else
{
lean_dec_ref(v_k_760_);
return v___x_768_;
}
}
}
case 2:
{
lean_object* v_decl_774_; lean_object* v_k_775_; lean_object* v_value_776_; lean_object* v___x_777_; 
v_decl_774_ = lean_ctor_get(v_code_747_, 0);
lean_inc_ref(v_decl_774_);
v_k_775_ = lean_ctor_get(v_code_747_, 1);
lean_inc_ref(v_k_775_);
lean_dec_ref(v_code_747_);
v_value_776_ = lean_ctor_get(v_decl_774_, 4);
lean_inc_ref(v_value_776_);
lean_dec_ref(v_decl_774_);
v___x_777_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_746_, v_value_776_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_dec_ref(v___x_777_);
v_code_747_ = v_k_775_;
goto _start;
}
else
{
lean_dec_ref(v_k_775_);
return v___x_777_;
}
}
case 3:
{
lean_object* v_fvarId_779_; lean_object* v_args_780_; uint8_t v___x_781_; lean_object* v___x_782_; 
v_fvarId_779_ = lean_ctor_get(v_code_747_, 0);
lean_inc(v_fvarId_779_);
v_args_780_ = lean_ctor_get(v_code_747_, 1);
lean_inc_ref(v_args_780_);
lean_dec_ref(v_code_747_);
v___x_781_ = 0;
v___x_782_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_781_, v_fvarId_779_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_808_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_808_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_808_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_808_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v_fvarId_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_787_ = lean_st_ref_take(v_a_748_);
v_fvarId_788_ = lean_ctor_get(v_a_783_, 0);
lean_inc(v_fvarId_788_);
lean_dec(v_a_783_);
v___x_789_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_787_, v_fvarId_788_);
v___x_790_ = lean_st_ref_set(v_a_748_, v___x_789_);
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = lean_array_get_size(v_args_780_);
v___x_793_ = lean_box(0);
v___x_794_ = lean_nat_dec_lt(v___x_791_, v___x_792_);
if (v___x_794_ == 0)
{
lean_object* v___x_796_; 
lean_dec_ref(v_args_780_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_793_);
v___x_796_ = v___x_785_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_793_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
else
{
uint8_t v___x_798_; 
v___x_798_ = lean_nat_dec_le(v___x_792_, v___x_792_);
if (v___x_798_ == 0)
{
if (v___x_794_ == 0)
{
lean_object* v___x_800_; 
lean_dec_ref(v_args_780_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_793_);
v___x_800_ = v___x_785_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_793_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
lean_del_object(v___x_785_);
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_792_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_780_, v___x_802_, v___x_803_, v___x_793_, v_a_748_, v_a_750_);
lean_dec_ref(v_args_780_);
return v___x_804_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
lean_del_object(v___x_785_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_792_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_780_, v___x_805_, v___x_806_, v___x_793_, v_a_748_, v_a_750_);
lean_dec_ref(v_args_780_);
return v___x_807_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_args_780_);
v_a_809_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_782_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_782_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
case 4:
{
lean_object* v_cases_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_839_; 
v_cases_817_ = lean_ctor_get(v_code_747_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v_code_747_);
if (v_isSharedCheck_839_ == 0)
{
v___x_819_ = v_code_747_;
v_isShared_820_ = v_isSharedCheck_839_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_cases_817_);
lean_dec(v_code_747_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_839_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_alts_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; 
v_alts_821_ = lean_ctor_get(v_cases_817_, 3);
lean_inc_ref(v_alts_821_);
lean_dec_ref(v_cases_817_);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_array_get_size(v_alts_821_);
v___x_824_ = lean_box(0);
v___x_825_ = lean_nat_dec_lt(v___x_822_, v___x_823_);
if (v___x_825_ == 0)
{
lean_object* v___x_827_; 
lean_dec_ref(v_alts_821_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 0);
lean_ctor_set(v___x_819_, 0, v___x_824_);
v___x_827_ = v___x_819_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_824_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
else
{
uint8_t v___x_829_; 
v___x_829_ = lean_nat_dec_le(v___x_823_, v___x_823_);
if (v___x_829_ == 0)
{
if (v___x_825_ == 0)
{
lean_object* v___x_831_; 
lean_dec_ref(v_alts_821_);
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 0);
lean_ctor_set(v___x_819_, 0, v___x_824_);
v___x_831_ = v___x_819_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_824_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; 
lean_del_object(v___x_819_);
v___x_833_ = ((size_t)0ULL);
v___x_834_ = lean_usize_of_nat(v___x_823_);
v___x_835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_746_, v_alts_821_, v___x_833_, v___x_834_, v___x_824_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec_ref(v_alts_821_);
return v___x_835_;
}
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
lean_del_object(v___x_819_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_823_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_746_, v_alts_821_, v___x_836_, v___x_837_, v___x_824_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec_ref(v_alts_821_);
return v___x_838_;
}
}
}
}
default: 
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_isSharedCheck_847_ = !lean_is_exclusive(v_code_747_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v_code_747_, 0);
lean_dec(v_unused_848_);
v___x_841_ = v_code_747_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_dec(v_code_747_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_box(0);
if (v_isShared_842_ == 0)
{
lean_ctor_set_tag(v___x_841_, 0);
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(uint8_t v_mustInline_849_, lean_object* v_as_850_, size_t v_i_851_, size_t v_stop_852_, lean_object* v_b_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___y_861_; uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_eq(v_i_851_, v_stop_852_);
if (v___x_867_ == 0)
{
lean_object* v___x_868_; 
v___x_868_ = lean_array_uget_borrowed(v_as_850_, v_i_851_);
switch(lean_obj_tag(v___x_868_))
{
case 0:
{
lean_object* v_code_869_; 
v_code_869_ = lean_ctor_get(v___x_868_, 2);
lean_inc_ref(v_code_869_);
v___y_861_ = v_code_869_;
goto v___jp_860_;
}
case 1:
{
lean_object* v_code_870_; 
v_code_870_ = lean_ctor_get(v___x_868_, 1);
lean_inc_ref(v_code_870_);
v___y_861_ = v_code_870_;
goto v___jp_860_;
}
default: 
{
lean_object* v_code_871_; 
v_code_871_ = lean_ctor_get(v___x_868_, 0);
lean_inc_ref(v_code_871_);
v___y_861_ = v_code_871_;
goto v___jp_860_;
}
}
}
else
{
lean_object* v___x_872_; 
v___x_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_872_, 0, v_b_853_);
return v___x_872_;
}
v___jp_860_:
{
lean_object* v___x_862_; 
v___x_862_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_849_, v___y_861_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; size_t v___x_864_; size_t v___x_865_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = ((size_t)1ULL);
v___x_865_ = lean_usize_add(v_i_851_, v___x_864_);
v_i_851_ = v___x_865_;
v_b_853_ = v_a_863_;
goto _start;
}
else
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0___boxed(lean_object* v_mustInline_873_, lean_object* v_as_874_, lean_object* v_i_875_, lean_object* v_stop_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
uint8_t v_mustInline_boxed_884_; size_t v_i_boxed_885_; size_t v_stop_boxed_886_; lean_object* v_res_887_; 
v_mustInline_boxed_884_ = lean_unbox(v_mustInline_873_);
v_i_boxed_885_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_stop_boxed_886_ = lean_unbox_usize(v_stop_876_);
lean_dec(v_stop_876_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_boxed_884_, v_as_874_, v_i_boxed_885_, v_stop_boxed_886_, v_b_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v_as_874_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go___boxed(lean_object* v_mustInline_888_, lean_object* v_code_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
uint8_t v_mustInline_boxed_896_; lean_object* v_res_897_; 
v_mustInline_boxed_896_ = lean_unbox(v_mustInline_888_);
v_res_897_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_boxed_896_, v_code_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object* v_s_898_, lean_object* v_code_899_, uint8_t v_mustInline_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_st_mk_ref(v_s_898_);
v___x_907_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_900_, v_code_899_, v___x_906_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
if (lean_obj_tag(v___x_907_) == 0)
{
lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_915_; 
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v___x_907_, 0);
lean_dec(v_unused_916_);
v___x_909_ = v___x_907_;
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
else
{
lean_dec(v___x_907_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_915_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_911_; lean_object* v___x_913_; 
v___x_911_ = lean_st_ref_get(v___x_906_);
lean_dec(v___x_906_);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_911_);
v___x_913_ = v___x_909_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_911_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v___x_906_);
v_a_917_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_907_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_907_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update___boxed(lean_object* v_s_925_, lean_object* v_code_926_, lean_object* v_mustInline_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_mustInline_boxed_933_; lean_object* v_res_934_; 
v_mustInline_boxed_933_ = lean_unbox(v_mustInline_927_);
v_res_934_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_s_925_, v_code_926_, v_mustInline_boxed_933_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec_ref(v_a_928_);
return v_res_934_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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

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
lean_object* v_head_173_; lean_object* v_tail_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_211_; 
v_head_173_ = lean_ctor_get(v_as_x27_165_, 0);
v_tail_174_ = lean_ctor_get(v_as_x27_165_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_as_x27_165_);
if (v_isSharedCheck_211_ == 0)
{
v___x_176_ = v_as_x27_165_;
v_isShared_177_ = v_isSharedCheck_211_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_tail_174_);
lean_inc(v_head_173_);
lean_dec(v_as_x27_165_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_211_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_210_; 
v_fst_178_ = lean_ctor_get(v_head_173_, 0);
v_snd_179_ = lean_ctor_get(v_head_173_, 1);
v_isSharedCheck_210_ = !lean_is_exclusive(v_head_173_);
if (v_isSharedCheck_210_ == 0)
{
v___x_181_ = v_head_173_;
v_isShared_182_ = v_isSharedCheck_210_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_inc(v_fst_178_);
lean_dec(v_head_173_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_210_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_178_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref(v___x_183_);
v___x_185_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1));
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 5);
lean_ctor_set(v___x_181_, 1, v___x_185_);
lean_ctor_set(v___x_181_, 0, v_b_166_);
v___x_187_ = v___x_181_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_b_166_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_201_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_188_ = 1;
v___x_189_ = l_Lean_Name_toString(v_a_184_, v___x_188_);
v___x_190_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
v___x_191_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3));
if (v_isShared_177_ == 0)
{
lean_ctor_set_tag(v___x_176_, 5);
lean_ctor_set(v___x_176_, 1, v___x_191_);
lean_ctor_set(v___x_176_, 0, v___x_190_);
v___x_193_ = v___x_176_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_200_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
lean_object* v___x_194_; uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_unbox(v_snd_179_);
lean_dec(v_snd_179_);
v___x_196_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v___x_195_, v___x_194_);
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_193_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_187_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
v_as_x27_165_ = v_tail_174_;
v_b_166_ = v___x_198_;
goto _start;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_del_object(v___x_181_);
lean_dec(v_snd_179_);
lean_del_object(v___x_176_);
lean_dec(v_tail_174_);
lean_dec(v_b_166_);
v_a_202_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_183_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_183_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___boxed(lean_object* v_as_x27_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_212_, v_b_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object* v_s_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_buckets_226_; lean_object* v_result_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_buckets_226_ = lean_ctor_get(v_s_220_, 1);
v_result_227_ = lean_box(0);
v___x_228_ = lean_box(0);
v___x_229_ = lean_array_get_size(v_buckets_226_);
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_nat_dec_lt(v___x_230_, v___x_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; 
v___x_232_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_228_, v_result_227_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
return v___x_232_;
}
else
{
size_t v___x_233_; size_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_233_ = lean_usize_of_nat(v___x_229_);
v___x_234_ = ((size_t)0ULL);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_buckets_226_, v___x_233_, v___x_234_, v___x_228_);
v___x_236_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_235_, v_result_227_, v_a_221_, v_a_222_, v_a_223_, v_a_224_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object* v_s_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_s_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_s_237_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(lean_object* v_as_244_, lean_object* v_as_x27_245_, lean_object* v_b_246_, lean_object* v_a_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_245_, v_b_246_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___boxed(lean_object* v_as_254_, lean_object* v_as_x27_255_, lean_object* v_b_256_, lean_object* v_a_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(v_as_254_, v_as_x27_255_, v_b_256_, v_a_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v_as_254_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_x_265_) == 0)
{
return v_x_264_;
}
else
{
lean_object* v_key_266_; lean_object* v_value_267_; lean_object* v_tail_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_291_; 
v_key_266_ = lean_ctor_get(v_x_265_, 0);
v_value_267_ = lean_ctor_get(v_x_265_, 1);
v_tail_268_ = lean_ctor_get(v_x_265_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_265_);
if (v_isSharedCheck_291_ == 0)
{
v___x_270_ = v_x_265_;
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_tail_268_);
lean_inc(v_value_267_);
lean_inc(v_key_266_);
lean_dec(v_x_265_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_291_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_272_; uint64_t v___x_273_; uint64_t v___x_274_; uint64_t v___x_275_; uint64_t v_fold_276_; uint64_t v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_272_ = lean_array_get_size(v_x_264_);
v___x_273_ = l_Lean_instHashableFVarId_hash(v_key_266_);
v___x_274_ = 32ULL;
v___x_275_ = lean_uint64_shift_right(v___x_273_, v___x_274_);
v_fold_276_ = lean_uint64_xor(v___x_273_, v___x_275_);
v___x_277_ = 16ULL;
v___x_278_ = lean_uint64_shift_right(v_fold_276_, v___x_277_);
v___x_279_ = lean_uint64_xor(v_fold_276_, v___x_278_);
v___x_280_ = lean_uint64_to_usize(v___x_279_);
v___x_281_ = lean_usize_of_nat(v___x_272_);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_sub(v___x_281_, v___x_282_);
v___x_284_ = lean_usize_land(v___x_280_, v___x_283_);
v___x_285_ = lean_array_uget_borrowed(v_x_264_, v___x_284_);
lean_inc(v___x_285_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 2, v___x_285_);
v___x_287_ = v___x_270_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_key_266_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_value_267_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v___x_285_);
v___x_287_ = v_reuseFailAlloc_290_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; 
v___x_288_ = lean_array_uset(v_x_264_, v___x_284_, v___x_287_);
v_x_264_ = v___x_288_;
v_x_265_ = v_tail_268_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(lean_object* v_i_292_, lean_object* v_source_293_, lean_object* v_target_294_){
_start:
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_array_get_size(v_source_293_);
v___x_296_ = lean_nat_dec_lt(v_i_292_, v___x_295_);
if (v___x_296_ == 0)
{
lean_dec_ref(v_source_293_);
lean_dec(v_i_292_);
return v_target_294_;
}
else
{
lean_object* v_es_297_; lean_object* v___x_298_; lean_object* v_source_299_; lean_object* v_target_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_es_297_ = lean_array_fget(v_source_293_, v_i_292_);
v___x_298_ = lean_box(0);
v_source_299_ = lean_array_fset(v_source_293_, v_i_292_, v___x_298_);
v_target_300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_target_294_, v_es_297_);
v___x_301_ = lean_unsigned_to_nat(1u);
v___x_302_ = lean_nat_add(v_i_292_, v___x_301_);
lean_dec(v_i_292_);
v_i_292_ = v___x_302_;
v_source_293_ = v_source_299_;
v_target_294_ = v_target_300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(lean_object* v_data_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_nbuckets_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_305_ = lean_array_get_size(v_data_304_);
v___x_306_ = lean_unsigned_to_nat(2u);
v_nbuckets_307_ = lean_nat_mul(v___x_305_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(0u);
v___x_309_ = lean_box(0);
v___x_310_ = lean_mk_array(v_nbuckets_307_, v___x_309_);
v___x_311_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v___x_308_, v_data_304_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(lean_object* v_a_312_, lean_object* v_x_313_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
uint8_t v___x_314_; 
v___x_314_ = 0;
return v___x_314_;
}
else
{
lean_object* v_key_315_; lean_object* v_tail_316_; uint8_t v___x_317_; 
v_key_315_ = lean_ctor_get(v_x_313_, 0);
v_tail_316_ = lean_ctor_get(v_x_313_, 2);
v___x_317_ = l_Lean_instBEqFVarId_beq(v_key_315_, v_a_312_);
if (v___x_317_ == 0)
{
v_x_313_ = v_tail_316_;
goto _start;
}
else
{
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(lean_object* v_a_319_, lean_object* v_x_320_){
_start:
{
uint8_t v_res_321_; lean_object* v_r_322_; 
v_res_321_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_319_, v_x_320_);
lean_dec(v_x_320_);
lean_dec(v_a_319_);
v_r_322_ = lean_box(v_res_321_);
return v_r_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(lean_object* v_a_323_, lean_object* v_b_324_, lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_dec(v_b_324_);
lean_dec(v_a_323_);
return v_x_325_;
}
else
{
lean_object* v_key_326_; lean_object* v_value_327_; lean_object* v_tail_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_340_; 
v_key_326_ = lean_ctor_get(v_x_325_, 0);
v_value_327_ = lean_ctor_get(v_x_325_, 1);
v_tail_328_ = lean_ctor_get(v_x_325_, 2);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_340_ == 0)
{
v___x_330_ = v_x_325_;
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_tail_328_);
lean_inc(v_value_327_);
lean_inc(v_key_326_);
lean_dec(v_x_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_340_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
uint8_t v___x_332_; 
v___x_332_ = l_Lean_instBEqFVarId_beq(v_key_326_, v_a_323_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_323_, v_b_324_, v_tail_328_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 2, v___x_333_);
v___x_335_ = v___x_330_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_key_326_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_value_327_);
lean_ctor_set(v_reuseFailAlloc_336_, 2, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
else
{
lean_object* v___x_338_; 
lean_dec(v_value_327_);
lean_dec(v_key_326_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 1, v_b_324_);
lean_ctor_set(v___x_330_, 0, v_a_323_);
v___x_338_ = v___x_330_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_323_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_b_324_);
lean_ctor_set(v_reuseFailAlloc_339_, 2, v_tail_328_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(lean_object* v_m_341_, lean_object* v_a_342_, lean_object* v_b_343_){
_start:
{
lean_object* v_size_344_; lean_object* v_buckets_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_388_; 
v_size_344_ = lean_ctor_get(v_m_341_, 0);
v_buckets_345_ = lean_ctor_get(v_m_341_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_m_341_);
if (v_isSharedCheck_388_ == 0)
{
v___x_347_ = v_m_341_;
v_isShared_348_ = v_isSharedCheck_388_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_buckets_345_);
lean_inc(v_size_344_);
lean_dec(v_m_341_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_388_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; uint64_t v___x_350_; uint64_t v___x_351_; uint64_t v___x_352_; uint64_t v_fold_353_; uint64_t v___x_354_; uint64_t v___x_355_; uint64_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v_bkt_362_; uint8_t v___x_363_; 
v___x_349_ = lean_array_get_size(v_buckets_345_);
v___x_350_ = l_Lean_instHashableFVarId_hash(v_a_342_);
v___x_351_ = 32ULL;
v___x_352_ = lean_uint64_shift_right(v___x_350_, v___x_351_);
v_fold_353_ = lean_uint64_xor(v___x_350_, v___x_352_);
v___x_354_ = 16ULL;
v___x_355_ = lean_uint64_shift_right(v_fold_353_, v___x_354_);
v___x_356_ = lean_uint64_xor(v_fold_353_, v___x_355_);
v___x_357_ = lean_uint64_to_usize(v___x_356_);
v___x_358_ = lean_usize_of_nat(v___x_349_);
v___x_359_ = ((size_t)1ULL);
v___x_360_ = lean_usize_sub(v___x_358_, v___x_359_);
v___x_361_ = lean_usize_land(v___x_357_, v___x_360_);
v_bkt_362_ = lean_array_uget_borrowed(v_buckets_345_, v___x_361_);
v___x_363_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_342_, v_bkt_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; lean_object* v_size_x27_365_; lean_object* v___x_366_; lean_object* v_buckets_x27_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_364_ = lean_unsigned_to_nat(1u);
v_size_x27_365_ = lean_nat_add(v_size_344_, v___x_364_);
lean_dec(v_size_344_);
lean_inc(v_bkt_362_);
v___x_366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_366_, 0, v_a_342_);
lean_ctor_set(v___x_366_, 1, v_b_343_);
lean_ctor_set(v___x_366_, 2, v_bkt_362_);
v_buckets_x27_367_ = lean_array_uset(v_buckets_345_, v___x_361_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(4u);
v___x_369_ = lean_nat_mul(v_size_x27_365_, v___x_368_);
v___x_370_ = lean_unsigned_to_nat(3u);
v___x_371_ = lean_nat_div(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_array_get_size(v_buckets_x27_367_);
v___x_373_ = lean_nat_dec_le(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
if (v___x_373_ == 0)
{
lean_object* v_val_374_; lean_object* v___x_376_; 
v_val_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_buckets_x27_367_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_val_374_);
lean_ctor_set(v___x_347_, 0, v_size_x27_365_);
v___x_376_ = v___x_347_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_val_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v_buckets_x27_367_);
lean_ctor_set(v___x_347_, 0, v_size_x27_365_);
v___x_379_ = v___x_347_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_size_x27_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_buckets_x27_367_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v___x_381_; lean_object* v_buckets_x27_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
lean_inc(v_bkt_362_);
v___x_381_ = lean_box(0);
v_buckets_x27_382_ = lean_array_uset(v_buckets_345_, v___x_361_, v___x_381_);
v___x_383_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_342_, v_b_343_, v_bkt_362_);
v___x_384_ = lean_array_uset(v_buckets_x27_382_, v___x_361_, v___x_383_);
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 1, v___x_384_);
v___x_386_ = v___x_347_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_size_344_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(lean_object* v_a_389_, lean_object* v_x_390_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v___x_391_; 
v___x_391_ = lean_box(0);
return v___x_391_;
}
else
{
lean_object* v_key_392_; lean_object* v_value_393_; lean_object* v_tail_394_; uint8_t v___x_395_; 
v_key_392_ = lean_ctor_get(v_x_390_, 0);
v_value_393_ = lean_ctor_get(v_x_390_, 1);
v_tail_394_ = lean_ctor_get(v_x_390_, 2);
v___x_395_ = l_Lean_instBEqFVarId_beq(v_key_392_, v_a_389_);
if (v___x_395_ == 0)
{
v_x_390_ = v_tail_394_;
goto _start;
}
else
{
lean_object* v___x_397_; 
lean_inc(v_value_393_);
v___x_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_397_, 0, v_value_393_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_398_, lean_object* v_x_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_398_, v_x_399_);
lean_dec(v_x_399_);
lean_dec(v_a_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(lean_object* v_m_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_buckets_403_; lean_object* v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; uint64_t v_fold_408_; uint64_t v___x_409_; uint64_t v___x_410_; uint64_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_buckets_403_ = lean_ctor_get(v_m_401_, 1);
v___x_404_ = lean_array_get_size(v_buckets_403_);
v___x_405_ = l_Lean_instHashableFVarId_hash(v_a_402_);
v___x_406_ = 32ULL;
v___x_407_ = lean_uint64_shift_right(v___x_405_, v___x_406_);
v_fold_408_ = lean_uint64_xor(v___x_405_, v___x_407_);
v___x_409_ = 16ULL;
v___x_410_ = lean_uint64_shift_right(v_fold_408_, v___x_409_);
v___x_411_ = lean_uint64_xor(v_fold_408_, v___x_410_);
v___x_412_ = lean_uint64_to_usize(v___x_411_);
v___x_413_ = lean_usize_of_nat(v___x_404_);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_sub(v___x_413_, v___x_414_);
v___x_416_ = lean_usize_land(v___x_412_, v___x_415_);
v___x_417_ = lean_array_uget_borrowed(v_buckets_403_, v___x_416_);
v___x_418_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_402_, v___x_417_);
return v___x_418_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg___boxed(lean_object* v_m_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_m_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object* v_s_422_, lean_object* v_fvarId_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_422_, v_fvarId_423_);
if (lean_obj_tag(v___x_424_) == 0)
{
uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = 0;
v___x_426_ = lean_box(v___x_425_);
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_422_, v_fvarId_423_, v___x_426_);
return v___x_427_;
}
else
{
lean_object* v_val_428_; uint8_t v___x_429_; 
v_val_428_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_val_428_);
lean_dec_ref(v___x_424_);
v___x_429_ = lean_unbox(v_val_428_);
lean_dec(v_val_428_);
if (v___x_429_ == 0)
{
uint8_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = 1;
v___x_431_ = lean_box(v___x_430_);
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_422_, v_fvarId_423_, v___x_431_);
return v___x_432_;
}
else
{
lean_dec(v_fvarId_423_);
return v_s_422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(lean_object* v_00_u03b2_433_, lean_object* v_m_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_434_, v_a_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(lean_object* v_00_u03b2_437_, lean_object* v_m_438_, lean_object* v_a_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(v_00_u03b2_437_, v_m_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_m_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(lean_object* v_00_u03b2_441_, lean_object* v_m_442_, lean_object* v_a_443_, lean_object* v_b_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_442_, v_a_443_, v_b_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(lean_object* v_00_u03b2_446_, lean_object* v_a_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_447_, v_x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_450_, lean_object* v_a_451_, lean_object* v_x_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(v_00_u03b2_450_, v_a_451_, v_x_452_);
lean_dec(v_x_452_);
lean_dec(v_a_451_);
return v_res_453_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_object* v_00_u03b2_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
uint8_t v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(v_00_u03b2_458_, v_a_459_, v_x_460_);
lean_dec(v_x_460_);
lean_dec(v_a_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3(lean_object* v_00_u03b2_463_, lean_object* v_data_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_data_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4(lean_object* v_00_u03b2_466_, lean_object* v_a_467_, lean_object* v_b_468_, lean_object* v_x_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_467_, v_b_468_, v_x_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_471_, lean_object* v_i_472_, lean_object* v_source_473_, lean_object* v_target_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v_i_472_, v_source_473_, v_target_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_x_477_, v_x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object* v_s_480_, lean_object* v_fvarId_481_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_480_, v_fvarId_481_);
if (lean_obj_tag(v___x_486_) == 0)
{
goto v___jp_482_;
}
else
{
lean_object* v_val_487_; uint8_t v___x_488_; 
v_val_487_ = lean_ctor_get(v___x_486_, 0);
lean_inc(v_val_487_);
lean_dec_ref(v___x_486_);
v___x_488_ = lean_unbox(v_val_487_);
lean_dec(v_val_487_);
if (v___x_488_ == 0)
{
goto v___jp_482_;
}
else
{
lean_dec(v_fvarId_481_);
return v_s_480_;
}
}
v___jp_482_:
{
uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = 1;
v___x_484_ = lean_box(v___x_483_);
v___x_485_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_480_, v_fvarId_481_, v___x_484_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object* v_s_489_, lean_object* v_fvarId_490_){
_start:
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_491_ = 2;
v___x_492_ = lean_box(v___x_491_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_489_, v_fvarId_490_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
return v_x_495_;
}
else
{
lean_object* v_key_496_; lean_object* v_value_497_; lean_object* v_tail_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_507_; 
v_key_496_ = lean_ctor_get(v_x_495_, 0);
v_value_497_ = lean_ctor_get(v_x_495_, 1);
v_tail_498_ = lean_ctor_get(v_x_495_, 2);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_507_ == 0)
{
v___x_500_ = v_x_495_;
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_tail_498_);
lean_inc(v_value_497_);
lean_inc(v_key_496_);
lean_dec(v_x_495_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_507_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
uint8_t v___x_502_; 
v___x_502_ = l_Lean_instBEqFVarId_beq(v_key_496_, v_a_494_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_494_, v_tail_498_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 2, v___x_503_);
v___x_505_ = v___x_500_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_key_496_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_value_497_);
lean_ctor_set(v_reuseFailAlloc_506_, 2, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_del_object(v___x_500_);
lean_dec(v_value_497_);
lean_dec(v_key_496_);
return v_tail_498_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg___boxed(lean_object* v_a_508_, lean_object* v_x_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_508_, v_x_509_);
lean_dec(v_a_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(lean_object* v_m_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_size_513_; lean_object* v_buckets_514_; lean_object* v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v___x_518_; uint64_t v_fold_519_; uint64_t v___x_520_; uint64_t v___x_521_; uint64_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; lean_object* v_bkt_528_; uint8_t v___x_529_; 
v_size_513_ = lean_ctor_get(v_m_511_, 0);
v_buckets_514_ = lean_ctor_get(v_m_511_, 1);
v___x_515_ = lean_array_get_size(v_buckets_514_);
v___x_516_ = l_Lean_instHashableFVarId_hash(v_a_512_);
v___x_517_ = 32ULL;
v___x_518_ = lean_uint64_shift_right(v___x_516_, v___x_517_);
v_fold_519_ = lean_uint64_xor(v___x_516_, v___x_518_);
v___x_520_ = 16ULL;
v___x_521_ = lean_uint64_shift_right(v_fold_519_, v___x_520_);
v___x_522_ = lean_uint64_xor(v_fold_519_, v___x_521_);
v___x_523_ = lean_uint64_to_usize(v___x_522_);
v___x_524_ = lean_usize_of_nat(v___x_515_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_sub(v___x_524_, v___x_525_);
v___x_527_ = lean_usize_land(v___x_523_, v___x_526_);
v_bkt_528_ = lean_array_uget_borrowed(v_buckets_514_, v___x_527_);
v___x_529_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_512_, v_bkt_528_);
if (v___x_529_ == 0)
{
return v_m_511_;
}
else
{
lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_542_; 
lean_inc(v_bkt_528_);
lean_inc_ref(v_buckets_514_);
lean_inc(v_size_513_);
v_isSharedCheck_542_ = !lean_is_exclusive(v_m_511_);
if (v_isSharedCheck_542_ == 0)
{
lean_object* v_unused_543_; lean_object* v_unused_544_; 
v_unused_543_ = lean_ctor_get(v_m_511_, 1);
lean_dec(v_unused_543_);
v_unused_544_ = lean_ctor_get(v_m_511_, 0);
lean_dec(v_unused_544_);
v___x_531_ = v_m_511_;
v_isShared_532_ = v_isSharedCheck_542_;
goto v_resetjp_530_;
}
else
{
lean_dec(v_m_511_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_542_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v_buckets_x27_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_533_ = lean_box(0);
v_buckets_x27_534_ = lean_array_uset(v_buckets_514_, v___x_527_, v___x_533_);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_sub(v_size_513_, v___x_535_);
lean_dec(v_size_513_);
v___x_537_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_512_, v_bkt_528_);
v___x_538_ = lean_array_uset(v_buckets_x27_534_, v___x_527_, v___x_537_);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 1, v___x_538_);
lean_ctor_set(v___x_531_, 0, v___x_536_);
v___x_540_ = v___x_531_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_536_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_545_, v_a_546_);
lean_dec(v_a_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object* v_s_548_, lean_object* v_fvarId_549_, lean_object* v_saved_x3f_550_){
_start:
{
if (lean_obj_tag(v_saved_x3f_550_) == 0)
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_s_548_, v_fvarId_549_);
lean_dec(v_fvarId_549_);
return v___x_551_;
}
else
{
lean_object* v_val_552_; lean_object* v___x_553_; 
v_val_552_ = lean_ctor_get(v_saved_x3f_550_, 0);
lean_inc(v_val_552_);
lean_dec_ref(v_saved_x3f_550_);
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_548_, v_fvarId_549_, v_val_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(lean_object* v_00_u03b2_554_, lean_object* v_m_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_555_, v_a_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(lean_object* v_00_u03b2_558_, lean_object* v_m_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(v_00_u03b2_558_, v_m_559_, v_a_560_);
lean_dec(v_a_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(lean_object* v_00_u03b2_562_, lean_object* v_a_563_, lean_object* v_x_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_563_, v_x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_566_, lean_object* v_a_567_, lean_object* v_x_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(v_00_u03b2_566_, v_a_567_, v_x_568_);
lean_dec(v_a_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(lean_object* v_arg_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
if (lean_obj_tag(v_arg_570_) == 1)
{
lean_object* v_fvarId_574_; uint8_t v___x_575_; lean_object* v___x_576_; 
v_fvarId_574_ = lean_ctor_get(v_arg_570_, 0);
lean_inc(v_fvarId_574_);
lean_dec_ref(v_arg_570_);
v___x_575_ = 0;
v___x_576_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_575_, v_fvarId_574_, v_a_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_594_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_594_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_594_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_594_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
if (lean_obj_tag(v_a_577_) == 1)
{
lean_object* v_val_581_; lean_object* v___x_582_; lean_object* v_fvarId_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_588_; 
v_val_581_ = lean_ctor_get(v_a_577_, 0);
lean_inc(v_val_581_);
lean_dec_ref(v_a_577_);
v___x_582_ = lean_st_ref_take(v_a_571_);
v_fvarId_583_ = lean_ctor_get(v_val_581_, 0);
lean_inc(v_fvarId_583_);
lean_dec(v_val_581_);
v___x_584_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v___x_582_, v_fvarId_583_);
v___x_585_ = lean_st_ref_set(v_a_571_, v___x_584_);
v___x_586_ = lean_box(0);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_586_);
v___x_588_ = v___x_579_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
else
{
lean_object* v___x_590_; lean_object* v___x_592_; 
lean_dec(v_a_577_);
v___x_590_ = lean_box(0);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_590_);
v___x_592_ = v___x_579_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___x_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
v_a_595_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_576_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_576_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; 
lean_dec(v_arg_570_);
v___x_603_ = lean_box(0);
v___x_604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_604_, 0, v___x_603_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg___boxed(lean_object* v_arg_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_605_, v_a_606_, v_a_607_);
lean_dec(v_a_607_);
lean_dec(v_a_606_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(lean_object* v_arg_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_610_, v_a_611_, v_a_613_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___boxed(lean_object* v_arg_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(v_arg_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(lean_object* v_as_626_, size_t v_i_627_, size_t v_stop_628_, lean_object* v_b_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_eq(v_i_627_, v_stop_628_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_634_ = lean_array_uget_borrowed(v_as_626_, v_i_627_);
lean_inc(v___x_634_);
v___x_635_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v___x_634_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; size_t v___x_637_; size_t v___x_638_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_add(v_i_627_, v___x_637_);
v_i_627_ = v___x_638_;
v_b_629_ = v_a_636_;
goto _start;
}
else
{
return v___x_635_;
}
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v_b_629_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg___boxed(lean_object* v_as_641_, lean_object* v_i_642_, lean_object* v_stop_643_, lean_object* v_b_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
size_t v_i_boxed_648_; size_t v_stop_boxed_649_; lean_object* v_res_650_; 
v_i_boxed_648_ = lean_unbox_usize(v_i_642_);
lean_dec(v_i_642_);
v_stop_boxed_649_ = lean_unbox_usize(v_stop_643_);
lean_dec(v_stop_643_);
v_res_650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_641_, v_i_boxed_648_, v_stop_boxed_649_, v_b_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v_as_641_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(lean_object* v_e_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
switch(lean_obj_tag(v_e_651_))
{
case 0:
{
lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_665_; 
v_isSharedCheck_665_ = !lean_is_exclusive(v_e_651_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_e_651_, 0);
lean_dec(v_unused_666_);
v___x_659_ = v_e_651_;
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
else
{
lean_dec(v_e_651_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_665_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = lean_box(0);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
case 3:
{
lean_object* v_args_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; uint8_t v___x_671_; 
v_args_667_ = lean_ctor_get(v_e_651_, 2);
lean_inc_ref(v_args_667_);
lean_dec_ref(v_e_651_);
v___x_668_ = lean_unsigned_to_nat(0u);
v___x_669_ = lean_array_get_size(v_args_667_);
v___x_670_ = lean_box(0);
v___x_671_ = lean_nat_dec_lt(v___x_668_, v___x_669_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
lean_dec_ref(v_args_667_);
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
return v___x_672_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = lean_nat_dec_le(v___x_669_, v___x_669_);
if (v___x_673_ == 0)
{
if (v___x_671_ == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v_args_667_);
v___x_674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_674_, 0, v___x_670_);
return v___x_674_;
}
else
{
size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v___x_675_ = ((size_t)0ULL);
v___x_676_ = lean_usize_of_nat(v___x_669_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_667_, v___x_675_, v___x_676_, v___x_670_, v_a_652_, v_a_654_);
lean_dec_ref(v_args_667_);
return v___x_677_;
}
}
else
{
size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
v___x_678_ = ((size_t)0ULL);
v___x_679_ = lean_usize_of_nat(v___x_669_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_667_, v___x_678_, v___x_679_, v___x_670_, v_a_652_, v_a_654_);
lean_dec_ref(v_args_667_);
return v___x_680_;
}
}
}
case 4:
{
lean_object* v_fvarId_681_; lean_object* v_args_682_; uint8_t v___x_683_; lean_object* v___x_684_; 
v_fvarId_681_ = lean_ctor_get(v_e_651_, 0);
lean_inc(v_fvarId_681_);
v_args_682_ = lean_ctor_get(v_e_651_, 1);
lean_inc_ref(v_args_682_);
lean_dec_ref(v_e_651_);
v___x_683_ = 0;
v___x_684_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_683_, v_fvarId_681_, v_a_654_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_715_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_715_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_715_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_715_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
if (lean_obj_tag(v_a_685_) == 1)
{
lean_object* v_val_689_; lean_object* v___x_690_; lean_object* v_fvarId_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_val_689_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_val_689_);
lean_dec_ref(v_a_685_);
v___x_690_ = lean_st_ref_take(v_a_652_);
v_fvarId_691_ = lean_ctor_get(v_val_689_, 0);
lean_inc(v_fvarId_691_);
lean_dec(v_val_689_);
v___x_692_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_690_, v_fvarId_691_);
v___x_693_ = lean_st_ref_set(v_a_652_, v___x_692_);
v___x_694_ = lean_unsigned_to_nat(0u);
v___x_695_ = lean_array_get_size(v_args_682_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_nat_dec_lt(v___x_694_, v___x_695_);
if (v___x_697_ == 0)
{
lean_object* v___x_699_; 
lean_dec_ref(v_args_682_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_696_);
v___x_699_ = v___x_687_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_696_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
uint8_t v___x_701_; 
v___x_701_ = lean_nat_dec_le(v___x_695_, v___x_695_);
if (v___x_701_ == 0)
{
if (v___x_697_ == 0)
{
lean_object* v___x_703_; 
lean_dec_ref(v_args_682_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_696_);
v___x_703_ = v___x_687_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_696_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
lean_del_object(v___x_687_);
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_695_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_682_, v___x_705_, v___x_706_, v___x_696_, v_a_652_, v_a_654_);
lean_dec_ref(v_args_682_);
return v___x_707_;
}
}
else
{
size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
lean_del_object(v___x_687_);
v___x_708_ = ((size_t)0ULL);
v___x_709_ = lean_usize_of_nat(v___x_695_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_682_, v___x_708_, v___x_709_, v___x_696_, v_a_652_, v_a_654_);
lean_dec_ref(v_args_682_);
return v___x_710_;
}
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_713_; 
lean_dec(v_a_685_);
lean_dec_ref(v_args_682_);
v___x_711_ = lean_box(0);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_711_);
v___x_713_ = v___x_687_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
else
{
lean_object* v_a_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_723_; 
lean_dec_ref(v_args_682_);
v_a_716_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_723_ == 0)
{
v___x_718_ = v___x_684_;
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_a_716_);
lean_dec(v___x_684_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_723_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_721_; 
if (v_isShared_719_ == 0)
{
v___x_721_ = v___x_718_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
default: 
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_e_651_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs___boxed(lean_object* v_e_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_e_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(lean_object* v_as_734_, size_t v_i_735_, size_t v_stop_736_, lean_object* v_b_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_734_, v_i_735_, v_stop_736_, v_b_737_, v___y_738_, v___y_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___boxed(lean_object* v_as_745_, lean_object* v_i_746_, lean_object* v_stop_747_, lean_object* v_b_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
size_t v_i_boxed_755_; size_t v_stop_boxed_756_; lean_object* v_res_757_; 
v_i_boxed_755_ = lean_unbox_usize(v_i_746_);
lean_dec(v_i_746_);
v_stop_boxed_756_ = lean_unbox_usize(v_stop_747_);
lean_dec(v_stop_747_);
v_res_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(v_as_745_, v_i_boxed_755_, v_stop_boxed_756_, v_b_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v_as_745_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(uint8_t v_mustInline_758_, lean_object* v_code_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
switch(lean_obj_tag(v_code_759_))
{
case 0:
{
lean_object* v_decl_766_; lean_object* v_k_767_; lean_object* v_value_768_; lean_object* v___x_769_; 
v_decl_766_ = lean_ctor_get(v_code_759_, 0);
lean_inc_ref(v_decl_766_);
v_k_767_ = lean_ctor_get(v_code_759_, 1);
lean_inc_ref(v_k_767_);
lean_dec_ref(v_code_759_);
v_value_768_ = lean_ctor_get(v_decl_766_, 3);
lean_inc(v_value_768_);
lean_dec_ref(v_decl_766_);
v___x_769_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_value_768_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_dec_ref(v___x_769_);
v_code_759_ = v_k_767_;
goto _start;
}
else
{
lean_dec_ref(v_k_767_);
return v___x_769_;
}
}
case 1:
{
lean_object* v_decl_771_; lean_object* v_k_772_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; 
v_decl_771_ = lean_ctor_get(v_code_759_, 0);
lean_inc_ref(v_decl_771_);
v_k_772_ = lean_ctor_get(v_code_759_, 1);
lean_inc_ref(v_k_772_);
lean_dec_ref(v_code_759_);
if (v_mustInline_758_ == 0)
{
v___y_774_ = v_a_760_;
v___y_775_ = v_a_761_;
v___y_776_ = v_a_762_;
v___y_777_ = v_a_763_;
v___y_778_ = v_a_764_;
goto v___jp_773_;
}
else
{
lean_object* v___x_782_; lean_object* v_fvarId_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = lean_st_ref_take(v_a_760_);
v_fvarId_783_ = lean_ctor_get(v_decl_771_, 0);
lean_inc(v_fvarId_783_);
v___x_784_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v___x_782_, v_fvarId_783_);
v___x_785_ = lean_st_ref_set(v_a_760_, v___x_784_);
v___y_774_ = v_a_760_;
v___y_775_ = v_a_761_;
v___y_776_ = v_a_762_;
v___y_777_ = v_a_763_;
v___y_778_ = v_a_764_;
goto v___jp_773_;
}
v___jp_773_:
{
lean_object* v_value_779_; lean_object* v___x_780_; 
v_value_779_ = lean_ctor_get(v_decl_771_, 4);
lean_inc_ref(v_value_779_);
lean_dec_ref(v_decl_771_);
v___x_780_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_758_, v_value_779_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_dec_ref(v___x_780_);
v_code_759_ = v_k_772_;
v_a_760_ = v___y_774_;
v_a_761_ = v___y_775_;
v_a_762_ = v___y_776_;
v_a_763_ = v___y_777_;
v_a_764_ = v___y_778_;
goto _start;
}
else
{
lean_dec_ref(v_k_772_);
return v___x_780_;
}
}
}
case 2:
{
lean_object* v_decl_786_; lean_object* v_k_787_; lean_object* v_value_788_; lean_object* v___x_789_; 
v_decl_786_ = lean_ctor_get(v_code_759_, 0);
lean_inc_ref(v_decl_786_);
v_k_787_ = lean_ctor_get(v_code_759_, 1);
lean_inc_ref(v_k_787_);
lean_dec_ref(v_code_759_);
v_value_788_ = lean_ctor_get(v_decl_786_, 4);
lean_inc_ref(v_value_788_);
lean_dec_ref(v_decl_786_);
v___x_789_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_758_, v_value_788_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_dec_ref(v___x_789_);
v_code_759_ = v_k_787_;
goto _start;
}
else
{
lean_dec_ref(v_k_787_);
return v___x_789_;
}
}
case 3:
{
lean_object* v_fvarId_791_; lean_object* v_args_792_; uint8_t v___x_793_; lean_object* v___x_794_; 
v_fvarId_791_ = lean_ctor_get(v_code_759_, 0);
lean_inc(v_fvarId_791_);
v_args_792_ = lean_ctor_get(v_code_759_, 1);
lean_inc_ref(v_args_792_);
lean_dec_ref(v_code_759_);
v___x_793_ = 0;
v___x_794_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_793_, v_fvarId_791_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_820_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_820_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_820_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_820_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_820_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v_fvarId_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_799_ = lean_st_ref_take(v_a_760_);
v_fvarId_800_ = lean_ctor_get(v_a_795_, 0);
lean_inc(v_fvarId_800_);
lean_dec(v_a_795_);
v___x_801_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_799_, v_fvarId_800_);
v___x_802_ = lean_st_ref_set(v_a_760_, v___x_801_);
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = lean_array_get_size(v_args_792_);
v___x_805_ = lean_box(0);
v___x_806_ = lean_nat_dec_lt(v___x_803_, v___x_804_);
if (v___x_806_ == 0)
{
lean_object* v___x_808_; 
lean_dec_ref(v_args_792_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_805_);
v___x_808_ = v___x_797_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
else
{
uint8_t v___x_810_; 
v___x_810_ = lean_nat_dec_le(v___x_804_, v___x_804_);
if (v___x_810_ == 0)
{
if (v___x_806_ == 0)
{
lean_object* v___x_812_; 
lean_dec_ref(v_args_792_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_805_);
v___x_812_ = v___x_797_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_805_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
size_t v___x_814_; size_t v___x_815_; lean_object* v___x_816_; 
lean_del_object(v___x_797_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = lean_usize_of_nat(v___x_804_);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_792_, v___x_814_, v___x_815_, v___x_805_, v_a_760_, v_a_762_);
lean_dec_ref(v_args_792_);
return v___x_816_;
}
}
else
{
size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
lean_del_object(v___x_797_);
v___x_817_ = ((size_t)0ULL);
v___x_818_ = lean_usize_of_nat(v___x_804_);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_792_, v___x_817_, v___x_818_, v___x_805_, v_a_760_, v_a_762_);
lean_dec_ref(v_args_792_);
return v___x_819_;
}
}
}
}
else
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_dec_ref(v_args_792_);
v_a_821_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_794_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_794_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
case 4:
{
lean_object* v_cases_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_851_; 
v_cases_829_ = lean_ctor_get(v_code_759_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v_code_759_);
if (v_isSharedCheck_851_ == 0)
{
v___x_831_ = v_code_759_;
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_cases_829_);
lean_dec(v_code_759_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_851_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_alts_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v_alts_833_ = lean_ctor_get(v_cases_829_, 3);
lean_inc_ref(v_alts_833_);
lean_dec_ref(v_cases_829_);
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_array_get_size(v_alts_833_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_nat_dec_lt(v___x_834_, v___x_835_);
if (v___x_837_ == 0)
{
lean_object* v___x_839_; 
lean_dec_ref(v_alts_833_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_839_ = v___x_831_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_836_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_le(v___x_835_, v___x_835_);
if (v___x_841_ == 0)
{
if (v___x_837_ == 0)
{
lean_object* v___x_843_; 
lean_dec_ref(v_alts_833_);
if (v_isShared_832_ == 0)
{
lean_ctor_set_tag(v___x_831_, 0);
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_843_ = v___x_831_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_836_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
lean_del_object(v___x_831_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = lean_usize_of_nat(v___x_835_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_758_, v_alts_833_, v___x_845_, v___x_846_, v___x_836_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec_ref(v_alts_833_);
return v___x_847_;
}
}
else
{
size_t v___x_848_; size_t v___x_849_; lean_object* v___x_850_; 
lean_del_object(v___x_831_);
v___x_848_ = ((size_t)0ULL);
v___x_849_ = lean_usize_of_nat(v___x_835_);
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_758_, v_alts_833_, v___x_848_, v___x_849_, v___x_836_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec_ref(v_alts_833_);
return v___x_850_;
}
}
}
}
default: 
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_859_; 
v_isSharedCheck_859_ = !lean_is_exclusive(v_code_759_);
if (v_isSharedCheck_859_ == 0)
{
lean_object* v_unused_860_; 
v_unused_860_ = lean_ctor_get(v_code_759_, 0);
lean_dec(v_unused_860_);
v___x_853_ = v_code_759_;
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
else
{
lean_dec(v_code_759_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_859_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_box(0);
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 0);
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(uint8_t v_mustInline_861_, lean_object* v_as_862_, size_t v_i_863_, size_t v_stop_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___y_873_; uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_eq(v_i_863_, v_stop_864_);
if (v___x_879_ == 0)
{
lean_object* v___x_880_; 
v___x_880_ = lean_array_uget_borrowed(v_as_862_, v_i_863_);
switch(lean_obj_tag(v___x_880_))
{
case 0:
{
lean_object* v_code_881_; 
v_code_881_ = lean_ctor_get(v___x_880_, 2);
lean_inc_ref(v_code_881_);
v___y_873_ = v_code_881_;
goto v___jp_872_;
}
case 1:
{
lean_object* v_code_882_; 
v_code_882_ = lean_ctor_get(v___x_880_, 1);
lean_inc_ref(v_code_882_);
v___y_873_ = v_code_882_;
goto v___jp_872_;
}
default: 
{
lean_object* v_code_883_; 
v_code_883_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_code_883_);
v___y_873_ = v_code_883_;
goto v___jp_872_;
}
}
}
else
{
lean_object* v___x_884_; 
v___x_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_884_, 0, v_b_865_);
return v___x_884_;
}
v___jp_872_:
{
lean_object* v___x_874_; 
v___x_874_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_861_, v___y_873_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; size_t v___x_876_; size_t v___x_877_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v___x_874_);
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_add(v_i_863_, v___x_876_);
v_i_863_ = v___x_877_;
v_b_865_ = v_a_875_;
goto _start;
}
else
{
return v___x_874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0___boxed(lean_object* v_mustInline_885_, lean_object* v_as_886_, lean_object* v_i_887_, lean_object* v_stop_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v_mustInline_boxed_896_; size_t v_i_boxed_897_; size_t v_stop_boxed_898_; lean_object* v_res_899_; 
v_mustInline_boxed_896_ = lean_unbox(v_mustInline_885_);
v_i_boxed_897_ = lean_unbox_usize(v_i_887_);
lean_dec(v_i_887_);
v_stop_boxed_898_ = lean_unbox_usize(v_stop_888_);
lean_dec(v_stop_888_);
v_res_899_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_boxed_896_, v_as_886_, v_i_boxed_897_, v_stop_boxed_898_, v_b_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v___y_890_);
lean_dec_ref(v_as_886_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go___boxed(lean_object* v_mustInline_900_, lean_object* v_code_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
uint8_t v_mustInline_boxed_908_; lean_object* v_res_909_; 
v_mustInline_boxed_908_ = lean_unbox(v_mustInline_900_);
v_res_909_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_boxed_908_, v_code_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec(v_a_904_);
lean_dec_ref(v_a_903_);
lean_dec(v_a_902_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object* v_s_910_, lean_object* v_code_911_, uint8_t v_mustInline_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_st_mk_ref(v_s_910_);
v___x_919_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_912_, v_code_911_, v___x_918_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_927_; 
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
lean_object* v_unused_928_; 
v_unused_928_ = lean_ctor_get(v___x_919_, 0);
lean_dec(v_unused_928_);
v___x_921_ = v___x_919_;
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
else
{
lean_dec(v___x_919_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_927_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_923_ = lean_st_ref_get(v___x_918_);
lean_dec(v___x_918_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v___x_918_);
v_a_929_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_919_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_919_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update___boxed(lean_object* v_s_937_, lean_object* v_code_938_, lean_object* v_mustInline_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
uint8_t v_mustInline_boxed_945_; lean_object* v_res_946_; 
v_mustInline_boxed_945_ = lean_unbox(v_mustInline_939_);
v_res_946_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_s_937_, v_code_938_, v_mustInline_boxed_945_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_946_;
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

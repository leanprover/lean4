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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___impl___boxed(lean_object*);
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
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___impl(uint8_t v_x_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_box(v_x_1_);
v___x_3_ = lean_obj_tag_nat(v___x_2_);
lean_dec(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_res_4_;
v_res_4_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___impl(v_x_1_);
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___impl___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_4__boxed_6_; lean_object* v_res_7_; 
v_x_4__boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorIdx___impl(v_x_4__boxed_6_);
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
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_12_ = stack[1].m_obj;
uint8_t v_t_13_ = stack[2].m_num;
lean_object* v_k_15_ = stack[4].m_obj;
lean_object* v_res_16_;
v_res_16_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(lean_box(0), v_ctorIdx_12_, v_t_13_, lean_box(0), v_k_15_);
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
uint8_t v_t_boxed_22_; lean_object* v_res_23_; 
v_t_boxed_22_ = lean_unbox(v_t_19_);
v_res_23_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_boxed_22_, v_h_20_, v_k_21_);
lean_dec(v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(lean_object* v_once_24_){
_start:
{
lean_inc(v_once_24_);
return v_once_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg___boxed(lean_object* v_once_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___redArg(v_once_25_);
lean_dec(v_once_25_);
return v_res_26_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(lean_object* v_motive_27_, uint8_t v_t_28_, lean_object* v_h_29_, lean_object* v_once_30_){
_start:
{
lean_inc(v_once_30_);
return v_once_30_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_28_ = stack[1].m_num;
lean_object* v_once_30_ = stack[3].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(lean_box(0), v_t_28_, lean_box(0), v_once_30_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim___boxed(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_once_35_){
_start:
{
uint8_t v_t_boxed_36_; lean_object* v_res_37_; 
v_t_boxed_36_ = lean_unbox(v_t_33_);
v_res_37_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_once_elim(v_motive_32_, v_t_boxed_36_, v_h_34_, v_once_35_);
lean_dec(v_once_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(lean_object* v_many_38_){
_start:
{
lean_inc(v_many_38_);
return v_many_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg___boxed(lean_object* v_many_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___redArg(v_many_39_);
lean_dec(v_many_39_);
return v_res_40_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(lean_object* v_motive_41_, uint8_t v_t_42_, lean_object* v_h_43_, lean_object* v_many_44_){
_start:
{
lean_inc(v_many_44_);
return v_many_44_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_42_ = stack[1].m_num;
lean_object* v_many_44_ = stack[3].m_obj;
lean_object* v_res_45_;
v_res_45_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(lean_box(0), v_t_42_, lean_box(0), v_many_44_);
stack->m_obj
 = v_res_45_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim___boxed(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_many_49_){
_start:
{
uint8_t v_t_boxed_50_; lean_object* v_res_51_; 
v_t_boxed_50_ = lean_unbox(v_t_47_);
v_res_51_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_many_elim(v_motive_46_, v_t_boxed_50_, v_h_48_, v_many_49_);
lean_dec(v_many_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(lean_object* v_mustInline_52_){
_start:
{
lean_inc(v_mustInline_52_);
return v_mustInline_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg___boxed(lean_object* v_mustInline_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___redArg(v_mustInline_53_);
lean_dec(v_mustInline_53_);
return v_res_54_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(lean_object* v_motive_55_, uint8_t v_t_56_, lean_object* v_h_57_, lean_object* v_mustInline_58_){
_start:
{
lean_inc(v_mustInline_58_);
return v_mustInline_58_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_56_ = stack[1].m_num;
lean_object* v_mustInline_58_ = stack[3].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(lean_box(0), v_t_56_, lean_box(0), v_mustInline_58_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim___boxed(lean_object* v_motive_60_, lean_object* v_t_61_, lean_object* v_h_62_, lean_object* v_mustInline_63_){
_start:
{
uint8_t v_t_boxed_64_; lean_object* v_res_65_; 
v_t_boxed_64_ = lean_unbox(v_t_61_);
v_res_65_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfo_mustInline_elim(v_motive_60_, v_t_boxed_64_, v_h_62_, v_mustInline_63_);
lean_dec(v_mustInline_63_);
return v_res_65_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_unsigned_to_nat(2u);
v___x_76_ = lean_nat_to_int(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_to_int(v___x_77_);
return v___x_78_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(uint8_t v_x_79_, lean_object* v_prec_80_){
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
v___x_104_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_82_ = v___x_104_;
goto v___jp_81_;
}
else
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
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
v___x_108_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_89_ = v___x_108_;
goto v___jp_88_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
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
v___x_112_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__6);
v___y_96_ = v___x_112_;
goto v___jp_95_;
}
else
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7, &l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7_once, _init_l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__7);
v___y_96_ = v___x_113_;
goto v___jp_95_;
}
}
}
v___jp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__1));
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
v___x_90_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__3));
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
v___x_97_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___closed__5));
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
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_79_ = stack[0].m_num;
lean_object* v_prec_80_ = stack[1].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v_x_79_, v_prec_80_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr___boxed(lean_object* v_x_115_, lean_object* v_prec_116_){
_start:
{
uint8_t v_x_171__boxed_117_; lean_object* v_res_118_; 
v_x_171__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v_x_171__boxed_117_, v_prec_116_);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(lean_object* v_as_142_, size_t v_i_143_, size_t v_stop_144_, lean_object* v_b_145_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_142_ = stack[0].m_obj;
size_t v_i_143_ = stack[1].m_num;
size_t v_stop_144_ = stack[2].m_num;
lean_object* v_b_145_ = stack[3].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_as_142_, v_i_143_, v_stop_144_, v_b_145_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2___boxed(lean_object* v_as_153_, lean_object* v_i_154_, lean_object* v_stop_155_, lean_object* v_b_156_){
_start:
{
size_t v_i_boxed_157_; size_t v_stop_boxed_158_; lean_object* v_res_159_; 
v_i_boxed_157_ = lean_unbox_usize(v_i_154_);
lean_dec(v_i_154_);
v_stop_boxed_158_ = lean_unbox_usize(v_stop_155_);
lean_dec(v_stop_155_);
v_res_159_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_as_153_, v_i_boxed_157_, v_stop_boxed_158_, v_b_156_);
lean_dec_ref(v_as_153_);
return v_res_159_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(lean_object* v_as_x27_166_, lean_object* v_b_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
if (lean_obj_tag(v_as_x27_166_) == 0)
{
lean_object* v___x_173_; 
v___x_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_173_, 0, v_b_167_);
return v___x_173_;
}
else
{
lean_object* v_head_174_; lean_object* v_tail_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; 
v_head_174_ = lean_ctor_get(v_as_x27_166_, 0);
v_tail_175_ = lean_ctor_get(v_as_x27_166_, 1);
v_fst_176_ = lean_ctor_get(v_head_174_, 0);
v_snd_177_ = lean_ctor_get(v_head_174_, 1);
lean_inc(v_fst_176_);
v___x_178_ = l_Lean_Compiler_LCNF_getBinderName(v_fst_176_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
v___x_180_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__1));
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v_b_167_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = 1;
v___x_183_ = l_Lean_Name_toString(v_a_179_, v___x_182_);
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
v___x_185_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___closed__3));
v___x_186_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = lean_unbox(v_snd_177_);
v___x_189_ = l_Lean_Compiler_LCNF_Simp_instReprFunDeclInfo_repr(v___x_188_, v___x_187_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_186_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_181_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v_as_x27_166_ = v_tail_175_;
v_b_167_ = v___x_191_;
goto _start;
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_b_167_);
v_a_193_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_178_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_178_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_166_ = stack[0].m_obj;
lean_object* v_b_167_ = stack[1].m_obj;
lean_object* v___y_168_ = stack[2].m_obj;
lean_object* v___y_169_ = stack[3].m_obj;
lean_object* v___y_170_ = stack[4].m_obj;
lean_object* v___y_171_ = stack[5].m_obj;
lean_object* v_res_201_;
v_res_201_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_166_, v_b_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg___boxed(lean_object* v_as_x27_202_, lean_object* v_b_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_202_, v_b_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v_as_x27_202_);
return v_res_209_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object* v_s_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_buckets_216_; lean_object* v_result_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_buckets_216_ = lean_ctor_get(v_s_210_, 1);
v_result_217_ = lean_box(0);
v___x_218_ = lean_box(0);
v___x_219_ = lean_array_get_size(v_buckets_216_);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_nat_dec_lt(v___x_220_, v___x_219_);
if (v___x_221_ == 0)
{
lean_object* v___x_222_; 
v___x_222_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_218_, v_result_217_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
return v___x_222_;
}
else
{
size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_223_ = lean_usize_of_nat(v___x_219_);
v___x_224_ = ((size_t)0ULL);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__2(v_buckets_216_, v___x_223_, v___x_224_, v___x_218_);
v___x_226_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_225_, v_result_217_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec(v___x_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_210_ = stack[0].m_obj;
lean_object* v_a_211_ = stack[1].m_obj;
lean_object* v_a_212_ = stack[2].m_obj;
lean_object* v_a_213_ = stack[3].m_obj;
lean_object* v_a_214_ = stack[4].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_s_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object* v_s_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_s_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec_ref(v_s_228_);
return v_res_234_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(lean_object* v_as_235_, lean_object* v_as_x27_236_, lean_object* v_b_237_, lean_object* v_a_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_236_, v_b_237_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
return v___x_244_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_235_ = stack[0].m_obj;
lean_object* v_as_x27_236_ = stack[1].m_obj;
lean_object* v_b_237_ = stack[2].m_obj;
lean_object* v___y_239_ = stack[4].m_obj;
lean_object* v___y_240_ = stack[5].m_obj;
lean_object* v___y_241_ = stack[6].m_obj;
lean_object* v___y_242_ = stack[7].m_obj;
lean_object* v_res_245_;
v_res_245_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(v_as_235_, v_as_x27_236_, v_b_237_, lean_box(0), v___y_239_, v___y_240_, v___y_241_, v___y_242_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___boxed(lean_object* v_as_246_, lean_object* v_as_x27_247_, lean_object* v_b_248_, lean_object* v_a_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(v_as_246_, v_as_x27_247_, v_b_248_, v_a_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v_as_x27_247_);
lean_dec(v_as_246_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
return v_x_256_;
}
else
{
lean_object* v_key_258_; lean_object* v_value_259_; lean_object* v_tail_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_283_; 
v_key_258_ = lean_ctor_get(v_x_257_, 0);
v_value_259_ = lean_ctor_get(v_x_257_, 1);
v_tail_260_ = lean_ctor_get(v_x_257_, 2);
v_isSharedCheck_283_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_283_ == 0)
{
v___x_262_ = v_x_257_;
v_isShared_263_ = v_isSharedCheck_283_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_tail_260_);
lean_inc(v_value_259_);
lean_inc(v_key_258_);
lean_dec(v_x_257_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_283_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; uint64_t v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v_fold_268_; uint64_t v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; size_t v___x_272_; size_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
v___x_264_ = lean_array_get_size(v_x_256_);
v___x_265_ = l_Lean_instHashableFVarId_hash(v_key_258_);
v___x_266_ = 32ULL;
v___x_267_ = lean_uint64_shift_right(v___x_265_, v___x_266_);
v_fold_268_ = lean_uint64_xor(v___x_265_, v___x_267_);
v___x_269_ = 16ULL;
v___x_270_ = lean_uint64_shift_right(v_fold_268_, v___x_269_);
v___x_271_ = lean_uint64_xor(v_fold_268_, v___x_270_);
v___x_272_ = lean_uint64_to_usize(v___x_271_);
v___x_273_ = lean_usize_of_nat(v___x_264_);
v___x_274_ = ((size_t)1ULL);
v___x_275_ = lean_usize_sub(v___x_273_, v___x_274_);
v___x_276_ = lean_usize_land(v___x_272_, v___x_275_);
v___x_277_ = lean_array_uget_borrowed(v_x_256_, v___x_276_);
lean_inc(v___x_277_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 2, v___x_277_);
v___x_279_ = v___x_262_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_key_258_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_value_259_);
lean_ctor_set(v_reuseFailAlloc_282_, 2, v___x_277_);
v___x_279_ = v_reuseFailAlloc_282_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
lean_object* v___x_280_; 
v___x_280_ = lean_array_uset(v_x_256_, v___x_276_, v___x_279_);
v_x_256_ = v___x_280_;
v_x_257_ = v_tail_260_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(lean_object* v_i_284_, lean_object* v_source_285_, lean_object* v_target_286_){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_array_get_size(v_source_285_);
v___x_288_ = lean_nat_dec_lt(v_i_284_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec_ref(v_source_285_);
lean_dec(v_i_284_);
return v_target_286_;
}
else
{
lean_object* v_es_289_; lean_object* v___x_290_; lean_object* v_source_291_; lean_object* v_target_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_es_289_ = lean_array_fget(v_source_285_, v_i_284_);
v___x_290_ = lean_box(0);
v_source_291_ = lean_array_fset(v_source_285_, v_i_284_, v___x_290_);
v_target_292_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_target_286_, v_es_289_);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_i_284_, v___x_293_);
lean_dec(v_i_284_);
v_i_284_ = v___x_294_;
v_source_285_ = v_source_291_;
v_target_286_ = v_target_292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(lean_object* v_data_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_nbuckets_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_297_ = lean_array_get_size(v_data_296_);
v___x_298_ = lean_unsigned_to_nat(2u);
v_nbuckets_299_ = lean_nat_mul(v___x_297_, v___x_298_);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_box(0);
v___x_302_ = lean_mk_array(v_nbuckets_299_, v___x_301_);
v___x_303_ = lean_array_propagate_mark(v_data_296_, v___x_302_);
v___x_304_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v___x_300_, v_data_296_, v___x_303_);
return v___x_304_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(lean_object* v_a_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
uint8_t v___x_307_; 
v___x_307_ = 0;
return v___x_307_;
}
else
{
lean_object* v_key_308_; lean_object* v_tail_309_; uint8_t v___x_310_; 
v_key_308_ = lean_ctor_get(v_x_306_, 0);
v_tail_309_ = lean_ctor_get(v_x_306_, 2);
v___x_310_ = l_Lean_instBEqFVarId_beq(v_key_308_, v_a_305_);
if (v___x_310_ == 0)
{
v_x_306_ = v_tail_309_;
goto _start;
}
else
{
return v___x_310_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_305_ = stack[0].m_obj;
lean_object* v_x_306_ = stack[1].m_obj;
uint8_t v_res_312_;
v_res_312_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_305_, v_x_306_);
stack->m_num = v_res_312_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(lean_object* v_a_313_, lean_object* v_x_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_313_, v_x_314_);
lean_dec(v_x_314_);
lean_dec(v_a_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(lean_object* v_a_317_, lean_object* v_b_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_dec(v_b_318_);
lean_dec(v_a_317_);
return v_x_319_;
}
else
{
lean_object* v_key_320_; lean_object* v_value_321_; lean_object* v_tail_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_334_; 
v_key_320_ = lean_ctor_get(v_x_319_, 0);
v_value_321_ = lean_ctor_get(v_x_319_, 1);
v_tail_322_ = lean_ctor_get(v_x_319_, 2);
v_isSharedCheck_334_ = !lean_is_exclusive(v_x_319_);
if (v_isSharedCheck_334_ == 0)
{
v___x_324_ = v_x_319_;
v_isShared_325_ = v_isSharedCheck_334_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_tail_322_);
lean_inc(v_value_321_);
lean_inc(v_key_320_);
lean_dec(v_x_319_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_334_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_instBEqFVarId_beq(v_key_320_, v_a_317_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_327_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_317_, v_b_318_, v_tail_322_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 2, v___x_327_);
v___x_329_ = v___x_324_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_key_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_value_321_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
else
{
lean_object* v___x_332_; 
lean_dec(v_value_321_);
lean_dec(v_key_320_);
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v_b_318_);
lean_ctor_set(v___x_324_, 0, v_a_317_);
v___x_332_ = v___x_324_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_317_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_b_318_);
lean_ctor_set(v_reuseFailAlloc_333_, 2, v_tail_322_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(lean_object* v_m_335_, lean_object* v_a_336_, lean_object* v_b_337_){
_start:
{
lean_object* v_size_338_; lean_object* v_buckets_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_382_; 
v_size_338_ = lean_ctor_get(v_m_335_, 0);
v_buckets_339_ = lean_ctor_get(v_m_335_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_m_335_);
if (v_isSharedCheck_382_ == 0)
{
v___x_341_ = v_m_335_;
v_isShared_342_ = v_isSharedCheck_382_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_buckets_339_);
lean_inc(v_size_338_);
lean_dec(v_m_335_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_382_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_343_; uint64_t v___x_344_; uint64_t v___x_345_; uint64_t v___x_346_; uint64_t v_fold_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; size_t v___x_354_; size_t v___x_355_; lean_object* v_bkt_356_; uint8_t v___x_357_; 
v___x_343_ = lean_array_get_size(v_buckets_339_);
v___x_344_ = l_Lean_instHashableFVarId_hash(v_a_336_);
v___x_345_ = 32ULL;
v___x_346_ = lean_uint64_shift_right(v___x_344_, v___x_345_);
v_fold_347_ = lean_uint64_xor(v___x_344_, v___x_346_);
v___x_348_ = 16ULL;
v___x_349_ = lean_uint64_shift_right(v_fold_347_, v___x_348_);
v___x_350_ = lean_uint64_xor(v_fold_347_, v___x_349_);
v___x_351_ = lean_uint64_to_usize(v___x_350_);
v___x_352_ = lean_usize_of_nat(v___x_343_);
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_sub(v___x_352_, v___x_353_);
v___x_355_ = lean_usize_land(v___x_351_, v___x_354_);
v_bkt_356_ = lean_array_uget_borrowed(v_buckets_339_, v___x_355_);
v___x_357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_336_, v_bkt_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v_size_x27_359_; lean_object* v___x_360_; lean_object* v_buckets_x27_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_358_ = lean_unsigned_to_nat(1u);
v_size_x27_359_ = lean_nat_add(v_size_338_, v___x_358_);
lean_dec(v_size_338_);
lean_inc(v_bkt_356_);
v___x_360_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_360_, 0, v_a_336_);
lean_ctor_set(v___x_360_, 1, v_b_337_);
lean_ctor_set(v___x_360_, 2, v_bkt_356_);
v_buckets_x27_361_ = lean_array_uset(v_buckets_339_, v___x_355_, v___x_360_);
v___x_362_ = lean_unsigned_to_nat(4u);
v___x_363_ = lean_nat_mul(v_size_x27_359_, v___x_362_);
v___x_364_ = lean_unsigned_to_nat(3u);
v___x_365_ = lean_nat_div(v___x_363_, v___x_364_);
lean_dec(v___x_363_);
v___x_366_ = lean_array_get_size(v_buckets_x27_361_);
v___x_367_ = lean_nat_dec_le(v___x_365_, v___x_366_);
lean_dec(v___x_365_);
if (v___x_367_ == 0)
{
lean_object* v_val_368_; lean_object* v___x_370_; 
v_val_368_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_buckets_x27_361_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v_val_368_);
lean_ctor_set(v___x_341_, 0, v_size_x27_359_);
v___x_370_ = v___x_341_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_size_x27_359_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_val_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
else
{
lean_object* v___x_373_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v_buckets_x27_361_);
lean_ctor_set(v___x_341_, 0, v_size_x27_359_);
v___x_373_ = v___x_341_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_size_x27_359_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v_buckets_x27_361_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
else
{
lean_object* v___x_375_; lean_object* v_buckets_x27_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
lean_inc(v_bkt_356_);
v___x_375_ = lean_box(0);
v_buckets_x27_376_ = lean_array_uset(v_buckets_339_, v___x_355_, v___x_375_);
v___x_377_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_336_, v_b_337_, v_bkt_356_);
v___x_378_ = lean_array_uset(v_buckets_x27_376_, v___x_355_, v___x_377_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_378_);
v___x_380_ = v___x_341_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_size_338_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(lean_object* v_a_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
else
{
lean_object* v_key_386_; lean_object* v_value_387_; lean_object* v_tail_388_; uint8_t v___x_389_; 
v_key_386_ = lean_ctor_get(v_x_384_, 0);
v_value_387_ = lean_ctor_get(v_x_384_, 1);
v_tail_388_ = lean_ctor_get(v_x_384_, 2);
v___x_389_ = l_Lean_instBEqFVarId_beq(v_key_386_, v_a_383_);
if (v___x_389_ == 0)
{
v_x_384_ = v_tail_388_;
goto _start;
}
else
{
lean_object* v___x_391_; 
lean_inc(v_value_387_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v_value_387_);
return v___x_391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(lean_object* v_a_392_, lean_object* v_x_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_392_, v_x_393_);
lean_dec(v_x_393_);
lean_dec(v_a_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(lean_object* v_m_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_buckets_397_; lean_object* v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v_fold_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_buckets_397_ = lean_ctor_get(v_m_395_, 1);
v___x_398_ = lean_array_get_size(v_buckets_397_);
v___x_399_ = l_Lean_instHashableFVarId_hash(v_a_396_);
v___x_400_ = 32ULL;
v___x_401_ = lean_uint64_shift_right(v___x_399_, v___x_400_);
v_fold_402_ = lean_uint64_xor(v___x_399_, v___x_401_);
v___x_403_ = 16ULL;
v___x_404_ = lean_uint64_shift_right(v_fold_402_, v___x_403_);
v___x_405_ = lean_uint64_xor(v_fold_402_, v___x_404_);
v___x_406_ = lean_uint64_to_usize(v___x_405_);
v___x_407_ = lean_usize_of_nat(v___x_398_);
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_sub(v___x_407_, v___x_408_);
v___x_410_ = lean_usize_land(v___x_406_, v___x_409_);
v___x_411_ = lean_array_uget_borrowed(v_buckets_397_, v___x_410_);
v___x_412_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_396_, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg___boxed(lean_object* v_m_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec_ref(v_m_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object* v_s_416_, lean_object* v_fvarId_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_416_, v_fvarId_417_);
if (lean_obj_tag(v___x_418_) == 0)
{
uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = 0;
v___x_420_ = lean_box(v___x_419_);
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_416_, v_fvarId_417_, v___x_420_);
return v___x_421_;
}
else
{
lean_object* v_val_422_; uint8_t v___x_423_; 
v_val_422_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v___x_418_, 1);
v___x_423_ = lean_unbox(v_val_422_);
lean_dec(v_val_422_);
if (v___x_423_ == 0)
{
uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = 1;
v___x_425_ = lean_box(v___x_424_);
v___x_426_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_416_, v_fvarId_417_, v___x_425_);
return v___x_426_;
}
else
{
lean_dec(v_fvarId_417_);
return v_s_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(lean_object* v_00_u03b2_427_, lean_object* v_m_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_428_, v_a_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(lean_object* v_00_u03b2_431_, lean_object* v_m_432_, lean_object* v_a_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(v_00_u03b2_431_, v_m_432_, v_a_433_);
lean_dec(v_a_433_);
lean_dec_ref(v_m_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(lean_object* v_00_u03b2_435_, lean_object* v_m_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_436_, v_a_437_, v_b_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(lean_object* v_00_u03b2_440_, lean_object* v_a_441_, lean_object* v_x_442_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_a_441_, v_x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_444_, lean_object* v_a_445_, lean_object* v_x_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(v_00_u03b2_444_, v_a_445_, v_x_446_);
lean_dec(v_x_446_);
lean_dec(v_a_445_);
return v_res_447_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_object* v_00_u03b2_448_, lean_object* v_a_449_, lean_object* v_x_450_){
_start:
{
uint8_t v___x_451_; 
v___x_451_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_449_, v_x_450_);
return v___x_451_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_449_ = stack[1].m_obj;
lean_object* v_x_450_ = stack[2].m_obj;
uint8_t v_res_452_;
v_res_452_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_box(0), v_a_449_, v_x_450_);
stack->m_num = v_res_452_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(lean_object* v_00_u03b2_453_, lean_object* v_a_454_, lean_object* v_x_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(v_00_u03b2_453_, v_a_454_, v_x_455_);
lean_dec(v_x_455_);
lean_dec(v_a_454_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3(lean_object* v_00_u03b2_458_, lean_object* v_data_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3___redArg(v_data_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_b_463_, lean_object* v_x_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__4___redArg(v_a_462_, v_b_463_, v_x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_466_, lean_object* v_i_467_, lean_object* v_source_468_, lean_object* v_target_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4___redArg(v_i_467_, v_source_468_, v_target_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__3_spec__4_spec__5___redArg(v_x_472_, v_x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object* v_s_475_, lean_object* v_fvarId_476_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_475_, v_fvarId_476_);
if (lean_obj_tag(v___x_481_) == 0)
{
goto v___jp_477_;
}
else
{
lean_object* v_val_482_; uint8_t v___x_483_; 
v_val_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_val_482_);
lean_dec_ref_known(v___x_481_, 1);
v___x_483_ = lean_unbox(v_val_482_);
lean_dec(v_val_482_);
if (v___x_483_ == 0)
{
goto v___jp_477_;
}
else
{
lean_dec(v_fvarId_476_);
return v_s_475_;
}
}
v___jp_477_:
{
uint8_t v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = 1;
v___x_479_ = lean_box(v___x_478_);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_475_, v_fvarId_476_, v___x_479_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object* v_s_484_, lean_object* v_fvarId_485_){
_start:
{
uint8_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = 2;
v___x_487_ = lean_box(v___x_486_);
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_484_, v_fvarId_485_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(lean_object* v_a_489_, lean_object* v_x_490_){
_start:
{
if (lean_obj_tag(v_x_490_) == 0)
{
return v_x_490_;
}
else
{
lean_object* v_key_491_; lean_object* v_value_492_; lean_object* v_tail_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_502_; 
v_key_491_ = lean_ctor_get(v_x_490_, 0);
v_value_492_ = lean_ctor_get(v_x_490_, 1);
v_tail_493_ = lean_ctor_get(v_x_490_, 2);
v_isSharedCheck_502_ = !lean_is_exclusive(v_x_490_);
if (v_isSharedCheck_502_ == 0)
{
v___x_495_ = v_x_490_;
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_tail_493_);
lean_inc(v_value_492_);
lean_inc(v_key_491_);
lean_dec(v_x_490_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_502_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
uint8_t v___x_497_; 
v___x_497_ = l_Lean_instBEqFVarId_beq(v_key_491_, v_a_489_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_489_, v_tail_493_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 2, v___x_498_);
v___x_500_ = v___x_495_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_key_491_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_value_492_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v___x_498_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
else
{
lean_del_object(v___x_495_);
lean_dec(v_value_492_);
lean_dec(v_key_491_);
return v_tail_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg___boxed(lean_object* v_a_503_, lean_object* v_x_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_503_, v_x_504_);
lean_dec(v_a_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(lean_object* v_m_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_size_508_; lean_object* v_buckets_509_; lean_object* v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v_fold_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v_bkt_523_; uint8_t v___x_524_; 
v_size_508_ = lean_ctor_get(v_m_506_, 0);
v_buckets_509_ = lean_ctor_get(v_m_506_, 1);
v___x_510_ = lean_array_get_size(v_buckets_509_);
v___x_511_ = l_Lean_instHashableFVarId_hash(v_a_507_);
v___x_512_ = 32ULL;
v___x_513_ = lean_uint64_shift_right(v___x_511_, v___x_512_);
v_fold_514_ = lean_uint64_xor(v___x_511_, v___x_513_);
v___x_515_ = 16ULL;
v___x_516_ = lean_uint64_shift_right(v_fold_514_, v___x_515_);
v___x_517_ = lean_uint64_xor(v_fold_514_, v___x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = lean_usize_of_nat(v___x_510_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_sub(v___x_519_, v___x_520_);
v___x_522_ = lean_usize_land(v___x_518_, v___x_521_);
v_bkt_523_ = lean_array_uget_borrowed(v_buckets_509_, v___x_522_);
v___x_524_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_a_507_, v_bkt_523_);
if (v___x_524_ == 0)
{
return v_m_506_;
}
else
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_537_; 
lean_inc(v_bkt_523_);
lean_inc_ref(v_buckets_509_);
lean_inc(v_size_508_);
v_isSharedCheck_537_ = !lean_is_exclusive(v_m_506_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; lean_object* v_unused_539_; 
v_unused_538_ = lean_ctor_get(v_m_506_, 1);
lean_dec(v_unused_538_);
v_unused_539_ = lean_ctor_get(v_m_506_, 0);
lean_dec(v_unused_539_);
v___x_526_ = v_m_506_;
v_isShared_527_ = v_isSharedCheck_537_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_m_506_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_537_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v_buckets_x27_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_528_ = lean_box(0);
v_buckets_x27_529_ = lean_array_uset(v_buckets_509_, v___x_522_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_sub(v_size_508_, v___x_530_);
lean_dec(v_size_508_);
v___x_532_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_507_, v_bkt_523_);
v___x_533_ = lean_array_uset(v_buckets_x27_529_, v___x_522_, v___x_532_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v___x_533_);
lean_ctor_set(v___x_526_, 0, v___x_531_);
v___x_535_ = v___x_526_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_531_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(lean_object* v_m_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_540_, v_a_541_);
lean_dec(v_a_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object* v_s_543_, lean_object* v_fvarId_544_, lean_object* v_saved_x3f_545_){
_start:
{
if (lean_obj_tag(v_saved_x3f_545_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_s_543_, v_fvarId_544_);
lean_dec(v_fvarId_544_);
return v___x_546_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_548_; 
v_val_547_ = lean_ctor_get(v_saved_x3f_545_, 0);
lean_inc(v_val_547_);
lean_dec_ref_known(v_saved_x3f_545_, 1);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_543_, v_fvarId_544_, v_val_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(lean_object* v_00_u03b2_549_, lean_object* v_m_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_550_, v_a_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(lean_object* v_00_u03b2_553_, lean_object* v_m_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(v_00_u03b2_553_, v_m_554_, v_a_555_);
lean_dec(v_a_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(lean_object* v_00_u03b2_557_, lean_object* v_a_558_, lean_object* v_x_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___redArg(v_a_558_, v_x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_561_, lean_object* v_a_562_, lean_object* v_x_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0_spec__0(v_00_u03b2_561_, v_a_562_, v_x_563_);
lean_dec(v_a_562_);
return v_res_564_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(lean_object* v_arg_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
if (lean_obj_tag(v_arg_565_) == 1)
{
lean_object* v_fvarId_569_; uint8_t v___x_570_; lean_object* v___x_571_; 
v_fvarId_569_ = lean_ctor_get(v_arg_565_, 0);
lean_inc(v_fvarId_569_);
lean_dec_ref_known(v_arg_565_, 1);
v___x_570_ = 0;
v___x_571_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_570_, v_fvarId_569_, v_a_567_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_589_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_589_ == 0)
{
v___x_574_ = v___x_571_;
v_isShared_575_ = v_isSharedCheck_589_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_a_572_);
lean_dec(v___x_571_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_589_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
if (lean_obj_tag(v_a_572_) == 1)
{
lean_object* v_val_576_; lean_object* v___x_577_; lean_object* v_fvarId_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v_val_576_ = lean_ctor_get(v_a_572_, 0);
lean_inc(v_val_576_);
lean_dec_ref_known(v_a_572_, 1);
v___x_577_ = lean_st_ref_take(v_a_566_);
v_fvarId_578_ = lean_ctor_get(v_val_576_, 0);
lean_inc(v_fvarId_578_);
lean_dec(v_val_576_);
v___x_579_ = lean_box(0);
v___x_580_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v___x_577_, v_fvarId_578_);
v___x_581_ = lean_st_ref_put(v_a_566_, v___x_580_);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_579_);
v___x_583_ = v___x_574_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_579_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
lean_object* v___x_585_; lean_object* v___x_587_; 
lean_dec(v_a_572_);
v___x_585_ = lean_box(0);
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 0, v___x_585_);
v___x_587_ = v___x_574_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
v_a_590_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_571_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_571_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_arg_565_);
v___x_598_ = lean_box(0);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_565_ = stack[0].m_obj;
lean_object* v_a_566_ = stack[1].m_obj;
lean_object* v_a_567_ = stack[2].m_obj;
lean_object* v_res_600_;
v_res_600_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_565_, v_a_566_, v_a_567_);
stack->m_obj
 = v_res_600_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg___boxed(lean_object* v_arg_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec(v_a_602_);
return v_res_605_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(lean_object* v_arg_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_606_, v_a_607_, v_a_609_);
return v___x_613_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_606_ = stack[0].m_obj;
lean_object* v_a_607_ = stack[1].m_obj;
lean_object* v_a_608_ = stack[2].m_obj;
lean_object* v_a_609_ = stack[3].m_obj;
lean_object* v_a_610_ = stack[4].m_obj;
lean_object* v_a_611_ = stack[5].m_obj;
lean_object* v_res_614_;
v_res_614_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(v_arg_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
stack->m_obj
 = v_res_614_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___boxed(lean_object* v_arg_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(v_arg_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec_ref(v_a_617_);
lean_dec(v_a_616_);
return v_res_622_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(lean_object* v_as_623_, size_t v_i_624_, size_t v_stop_625_, lean_object* v_b_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v___x_630_; 
v___x_630_ = lean_usize_dec_eq(v_i_624_, v_stop_625_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_631_ = lean_array_uget_borrowed(v_as_623_, v_i_624_);
lean_inc(v___x_631_);
v___x_632_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v___x_631_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; size_t v___x_634_; size_t v___x_635_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_add(v_i_624_, v___x_634_);
v_i_624_ = v___x_635_;
v_b_626_ = v_a_633_;
goto _start;
}
else
{
return v___x_632_;
}
}
else
{
lean_object* v___x_637_; 
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v_b_626_);
return v___x_637_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_623_ = stack[0].m_obj;
size_t v_i_624_ = stack[1].m_num;
size_t v_stop_625_ = stack[2].m_num;
lean_object* v_b_626_ = stack[3].m_obj;
lean_object* v___y_627_ = stack[4].m_obj;
lean_object* v___y_628_ = stack[5].m_obj;
lean_object* v_res_638_;
v_res_638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_623_, v_i_624_, v_stop_625_, v_b_626_, v___y_627_, v___y_628_);
stack->m_obj
 = v_res_638_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg___boxed(lean_object* v_as_639_, lean_object* v_i_640_, lean_object* v_stop_641_, lean_object* v_b_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
size_t v_i_boxed_646_; size_t v_stop_boxed_647_; lean_object* v_res_648_; 
v_i_boxed_646_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_stop_boxed_647_ = lean_unbox_usize(v_stop_641_);
lean_dec(v_stop_641_);
v_res_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_639_, v_i_boxed_646_, v_stop_boxed_647_, v_b_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v_as_639_);
return v_res_648_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
switch(lean_obj_tag(v_e_649_))
{
case 3:
{
lean_object* v_args_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v_args_656_ = lean_ctor_get(v_e_649_, 2);
lean_inc_ref(v_args_656_);
lean_dec_ref_known(v_e_649_, 3);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_array_get_size(v_args_656_);
v___x_659_ = lean_box(0);
v___x_660_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_args_656_);
v___x_661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
return v___x_661_;
}
else
{
uint8_t v___x_662_; 
v___x_662_ = lean_nat_dec_le(v___x_658_, v___x_658_);
if (v___x_662_ == 0)
{
if (v___x_660_ == 0)
{
lean_object* v___x_663_; 
lean_dec_ref(v_args_656_);
v___x_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_663_, 0, v___x_659_);
return v___x_663_;
}
else
{
size_t v___x_664_; size_t v___x_665_; lean_object* v___x_666_; 
v___x_664_ = ((size_t)0ULL);
v___x_665_ = lean_usize_of_nat(v___x_658_);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_656_, v___x_664_, v___x_665_, v___x_659_, v_a_650_, v_a_652_);
lean_dec_ref(v_args_656_);
return v___x_666_;
}
}
else
{
size_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
v___x_667_ = ((size_t)0ULL);
v___x_668_ = lean_usize_of_nat(v___x_658_);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_656_, v___x_667_, v___x_668_, v___x_659_, v_a_650_, v_a_652_);
lean_dec_ref(v_args_656_);
return v___x_669_;
}
}
}
case 4:
{
lean_object* v_fvarId_670_; lean_object* v_args_671_; uint8_t v___x_672_; lean_object* v___x_673_; 
v_fvarId_670_ = lean_ctor_get(v_e_649_, 0);
lean_inc(v_fvarId_670_);
v_args_671_ = lean_ctor_get(v_e_649_, 1);
lean_inc_ref(v_args_671_);
lean_dec_ref_known(v_e_649_, 2);
v___x_672_ = 0;
v___x_673_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_672_, v_fvarId_670_, v_a_652_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_704_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_704_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_704_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_704_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
if (lean_obj_tag(v_a_674_) == 1)
{
lean_object* v_val_678_; lean_object* v___x_679_; lean_object* v_fvarId_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_val_678_ = lean_ctor_get(v_a_674_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v_a_674_, 1);
v___x_679_ = lean_st_ref_take(v_a_650_);
v_fvarId_680_ = lean_ctor_get(v_val_678_, 0);
lean_inc(v_fvarId_680_);
lean_dec(v_val_678_);
v___x_681_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_679_, v_fvarId_680_);
v___x_682_ = lean_st_ref_put(v_a_650_, v___x_681_);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_array_get_size(v_args_671_);
v___x_685_ = lean_box(0);
v___x_686_ = lean_nat_dec_lt(v___x_683_, v___x_684_);
if (v___x_686_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref(v_args_671_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_685_);
v___x_688_ = v___x_676_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_685_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
uint8_t v___x_690_; 
v___x_690_ = lean_nat_dec_le(v___x_684_, v___x_684_);
if (v___x_690_ == 0)
{
if (v___x_686_ == 0)
{
lean_object* v___x_692_; 
lean_dec_ref(v_args_671_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_685_);
v___x_692_ = v___x_676_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_685_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
lean_del_object(v___x_676_);
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_684_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_671_, v___x_694_, v___x_695_, v___x_685_, v_a_650_, v_a_652_);
lean_dec_ref(v_args_671_);
return v___x_696_;
}
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
lean_del_object(v___x_676_);
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_684_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_671_, v___x_697_, v___x_698_, v___x_685_, v_a_650_, v_a_652_);
lean_dec_ref(v_args_671_);
return v___x_699_;
}
}
}
else
{
lean_object* v___x_700_; lean_object* v___x_702_; 
lean_dec(v_a_674_);
lean_dec_ref(v_args_671_);
v___x_700_ = lean_box(0);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_700_);
v___x_702_ = v___x_676_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v_args_671_);
v_a_705_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_673_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_673_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
default: 
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v_e_649_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_649_ = stack[0].m_obj;
lean_object* v_a_650_ = stack[1].m_obj;
lean_object* v_a_651_ = stack[2].m_obj;
lean_object* v_a_652_ = stack[3].m_obj;
lean_object* v_a_653_ = stack[4].m_obj;
lean_object* v_a_654_ = stack[5].m_obj;
lean_object* v_res_715_;
v_res_715_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_e_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs___boxed(lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
return v_res_723_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(lean_object* v_as_724_, size_t v_i_725_, size_t v_stop_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_724_, v_i_725_, v_stop_726_, v_b_727_, v___y_728_, v___y_730_);
return v___x_734_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_724_ = stack[0].m_obj;
size_t v_i_725_ = stack[1].m_num;
size_t v_stop_726_ = stack[2].m_num;
lean_object* v_b_727_ = stack[3].m_obj;
lean_object* v___y_728_ = stack[4].m_obj;
lean_object* v___y_729_ = stack[5].m_obj;
lean_object* v___y_730_ = stack[6].m_obj;
lean_object* v___y_731_ = stack[7].m_obj;
lean_object* v___y_732_ = stack[8].m_obj;
lean_object* v_res_735_;
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(v_as_724_, v_i_725_, v_stop_726_, v_b_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
stack->m_obj
 = v_res_735_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___boxed(lean_object* v_as_736_, lean_object* v_i_737_, lean_object* v_stop_738_, lean_object* v_b_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
size_t v_i_boxed_746_; size_t v_stop_boxed_747_; lean_object* v_res_748_; 
v_i_boxed_746_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_stop_boxed_747_ = lean_unbox_usize(v_stop_738_);
lean_dec(v_stop_738_);
v_res_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(v_as_736_, v_i_boxed_746_, v_stop_boxed_747_, v_b_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v_as_736_);
return v_res_748_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(uint8_t v_mustInline_749_, lean_object* v_code_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
switch(lean_obj_tag(v_code_750_))
{
case 0:
{
lean_object* v_decl_757_; lean_object* v_k_758_; lean_object* v_value_759_; lean_object* v___x_760_; 
v_decl_757_ = lean_ctor_get(v_code_750_, 0);
lean_inc_ref(v_decl_757_);
v_k_758_ = lean_ctor_get(v_code_750_, 1);
lean_inc_ref(v_k_758_);
lean_dec_ref_known(v_code_750_, 2);
v_value_759_ = lean_ctor_get(v_decl_757_, 3);
lean_inc(v_value_759_);
lean_dec_ref(v_decl_757_);
v___x_760_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_value_759_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_dec_ref_known(v___x_760_, 1);
v_code_750_ = v_k_758_;
goto _start;
}
else
{
lean_dec_ref(v_k_758_);
return v___x_760_;
}
}
case 1:
{
lean_object* v_decl_762_; lean_object* v_k_763_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; 
v_decl_762_ = lean_ctor_get(v_code_750_, 0);
lean_inc_ref(v_decl_762_);
v_k_763_ = lean_ctor_get(v_code_750_, 1);
lean_inc_ref(v_k_763_);
lean_dec_ref_known(v_code_750_, 2);
if (v_mustInline_749_ == 0)
{
v___y_765_ = v_a_751_;
v___y_766_ = v_a_752_;
v___y_767_ = v_a_753_;
v___y_768_ = v_a_754_;
v___y_769_ = v_a_755_;
goto v___jp_764_;
}
else
{
lean_object* v___x_773_; lean_object* v_fvarId_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_773_ = lean_st_ref_take(v_a_751_);
v_fvarId_774_ = lean_ctor_get(v_decl_762_, 0);
lean_inc(v_fvarId_774_);
v___x_775_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v___x_773_, v_fvarId_774_);
v___x_776_ = lean_st_ref_put(v_a_751_, v___x_775_);
v___y_765_ = v_a_751_;
v___y_766_ = v_a_752_;
v___y_767_ = v_a_753_;
v___y_768_ = v_a_754_;
v___y_769_ = v_a_755_;
goto v___jp_764_;
}
v___jp_764_:
{
lean_object* v_value_770_; lean_object* v___x_771_; 
v_value_770_ = lean_ctor_get(v_decl_762_, 4);
lean_inc_ref(v_value_770_);
lean_dec_ref(v_decl_762_);
v___x_771_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_749_, v_value_770_, v___y_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_dec_ref_known(v___x_771_, 1);
v_code_750_ = v_k_763_;
v_a_751_ = v___y_765_;
v_a_752_ = v___y_766_;
v_a_753_ = v___y_767_;
v_a_754_ = v___y_768_;
v_a_755_ = v___y_769_;
goto _start;
}
else
{
lean_dec_ref(v_k_763_);
return v___x_771_;
}
}
}
case 2:
{
lean_object* v_decl_777_; lean_object* v_k_778_; lean_object* v_value_779_; lean_object* v___x_780_; 
v_decl_777_ = lean_ctor_get(v_code_750_, 0);
lean_inc_ref(v_decl_777_);
v_k_778_ = lean_ctor_get(v_code_750_, 1);
lean_inc_ref(v_k_778_);
lean_dec_ref_known(v_code_750_, 2);
v_value_779_ = lean_ctor_get(v_decl_777_, 4);
lean_inc_ref(v_value_779_);
lean_dec_ref(v_decl_777_);
v___x_780_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_749_, v_value_779_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_dec_ref_known(v___x_780_, 1);
v_code_750_ = v_k_778_;
goto _start;
}
else
{
lean_dec_ref(v_k_778_);
return v___x_780_;
}
}
case 3:
{
lean_object* v_fvarId_782_; lean_object* v_args_783_; uint8_t v___x_784_; lean_object* v___x_785_; 
v_fvarId_782_ = lean_ctor_get(v_code_750_, 0);
lean_inc(v_fvarId_782_);
v_args_783_ = lean_ctor_get(v_code_750_, 1);
lean_inc_ref(v_args_783_);
lean_dec_ref_known(v_code_750_, 2);
v___x_784_ = 0;
v___x_785_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_784_, v_fvarId_782_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_811_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_811_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_811_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_811_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v_fvarId_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_790_ = lean_st_ref_take(v_a_751_);
v_fvarId_791_ = lean_ctor_get(v_a_786_, 0);
lean_inc(v_fvarId_791_);
lean_dec(v_a_786_);
v___x_792_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_790_, v_fvarId_791_);
v___x_793_ = lean_st_ref_put(v_a_751_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_args_783_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_797_ == 0)
{
lean_object* v___x_799_; 
lean_dec_ref(v_args_783_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_796_);
v___x_799_ = v___x_788_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_796_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
else
{
uint8_t v___x_801_; 
v___x_801_ = lean_nat_dec_le(v___x_795_, v___x_795_);
if (v___x_801_ == 0)
{
if (v___x_797_ == 0)
{
lean_object* v___x_803_; 
lean_dec_ref(v_args_783_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_796_);
v___x_803_ = v___x_788_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_796_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
lean_del_object(v___x_788_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_795_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_783_, v___x_805_, v___x_806_, v___x_796_, v_a_751_, v_a_753_);
lean_dec_ref(v_args_783_);
return v___x_807_;
}
}
else
{
size_t v___x_808_; size_t v___x_809_; lean_object* v___x_810_; 
lean_del_object(v___x_788_);
v___x_808_ = ((size_t)0ULL);
v___x_809_ = lean_usize_of_nat(v___x_795_);
v___x_810_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_783_, v___x_808_, v___x_809_, v___x_796_, v_a_751_, v_a_753_);
lean_dec_ref(v_args_783_);
return v___x_810_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_args_783_);
v_a_812_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_785_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_785_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
case 4:
{
lean_object* v_cases_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_842_; 
v_cases_820_ = lean_ctor_get(v_code_750_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_code_750_);
if (v_isSharedCheck_842_ == 0)
{
v___x_822_ = v_code_750_;
v_isShared_823_ = v_isSharedCheck_842_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_cases_820_);
lean_dec(v_code_750_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_842_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_alts_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_alts_824_ = lean_ctor_get(v_cases_820_, 3);
lean_inc_ref(v_alts_824_);
lean_dec_ref(v_cases_820_);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_array_get_size(v_alts_824_);
v___x_827_ = lean_box(0);
v___x_828_ = lean_nat_dec_lt(v___x_825_, v___x_826_);
if (v___x_828_ == 0)
{
lean_object* v___x_830_; 
lean_dec_ref(v_alts_824_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_827_);
v___x_830_ = v___x_822_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_827_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
uint8_t v___x_832_; 
v___x_832_ = lean_nat_dec_le(v___x_826_, v___x_826_);
if (v___x_832_ == 0)
{
if (v___x_828_ == 0)
{
lean_object* v___x_834_; 
lean_dec_ref(v_alts_824_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_827_);
v___x_834_ = v___x_822_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_827_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
lean_del_object(v___x_822_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_826_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_749_, v_alts_824_, v___x_836_, v___x_837_, v___x_827_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec_ref(v_alts_824_);
return v___x_838_;
}
}
else
{
size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
lean_del_object(v___x_822_);
v___x_839_ = ((size_t)0ULL);
v___x_840_ = lean_usize_of_nat(v___x_826_);
v___x_841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_749_, v_alts_824_, v___x_839_, v___x_840_, v___x_827_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec_ref(v_alts_824_);
return v___x_841_;
}
}
}
}
default: 
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_isSharedCheck_850_ = !lean_is_exclusive(v_code_750_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v_code_750_, 0);
lean_dec(v_unused_851_);
v___x_844_ = v_code_750_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_code_750_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_box(0);
if (v_isShared_845_ == 0)
{
lean_ctor_set_tag(v___x_844_, 0);
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_mustInline_749_ = stack[0].m_num;
lean_object* v_code_750_ = stack[1].m_obj;
lean_object* v_a_751_ = stack[2].m_obj;
lean_object* v_a_752_ = stack[3].m_obj;
lean_object* v_a_753_ = stack[4].m_obj;
lean_object* v_a_754_ = stack[5].m_obj;
lean_object* v_a_755_ = stack[6].m_obj;
lean_object* v_res_852_;
v_res_852_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_749_, v_code_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
stack->m_obj
 = v_res_852_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(uint8_t v_mustInline_853_, lean_object* v_as_854_, size_t v_i_855_, size_t v_stop_856_, lean_object* v_b_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v___y_865_; uint8_t v___x_871_; 
v___x_871_ = lean_usize_dec_eq(v_i_855_, v_stop_856_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; 
v___x_872_ = lean_array_uget_borrowed(v_as_854_, v_i_855_);
switch(lean_obj_tag(v___x_872_))
{
case 0:
{
lean_object* v_code_873_; 
v_code_873_ = lean_ctor_get(v___x_872_, 2);
lean_inc_ref(v_code_873_);
v___y_865_ = v_code_873_;
goto v___jp_864_;
}
case 1:
{
lean_object* v_code_874_; 
v_code_874_ = lean_ctor_get(v___x_872_, 1);
lean_inc_ref(v_code_874_);
v___y_865_ = v_code_874_;
goto v___jp_864_;
}
default: 
{
lean_object* v_code_875_; 
v_code_875_ = lean_ctor_get(v___x_872_, 0);
lean_inc_ref(v_code_875_);
v___y_865_ = v_code_875_;
goto v___jp_864_;
}
}
}
else
{
lean_object* v___x_876_; 
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v_b_857_);
return v___x_876_;
}
v___jp_864_:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_853_, v___y_865_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; size_t v___x_868_; size_t v___x_869_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_add(v_i_855_, v___x_868_);
v_i_855_ = v___x_869_;
v_b_857_ = v_a_867_;
goto _start;
}
else
{
return v___x_866_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_mustInline_853_ = stack[0].m_num;
lean_object* v_as_854_ = stack[1].m_obj;
size_t v_i_855_ = stack[2].m_num;
size_t v_stop_856_ = stack[3].m_num;
lean_object* v_b_857_ = stack[4].m_obj;
lean_object* v___y_858_ = stack[5].m_obj;
lean_object* v___y_859_ = stack[6].m_obj;
lean_object* v___y_860_ = stack[7].m_obj;
lean_object* v___y_861_ = stack[8].m_obj;
lean_object* v___y_862_ = stack[9].m_obj;
lean_object* v_res_877_;
v_res_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_853_, v_as_854_, v_i_855_, v_stop_856_, v_b_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
stack->m_obj
 = v_res_877_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0___boxed(lean_object* v_mustInline_878_, lean_object* v_as_879_, lean_object* v_i_880_, lean_object* v_stop_881_, lean_object* v_b_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v_mustInline_boxed_889_; size_t v_i_boxed_890_; size_t v_stop_boxed_891_; lean_object* v_res_892_; 
v_mustInline_boxed_889_ = lean_unbox(v_mustInline_878_);
v_i_boxed_890_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_stop_boxed_891_ = lean_unbox_usize(v_stop_881_);
lean_dec(v_stop_881_);
v_res_892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_boxed_889_, v_as_879_, v_i_boxed_890_, v_stop_boxed_891_, v_b_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v_as_879_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go___boxed(lean_object* v_mustInline_893_, lean_object* v_code_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
uint8_t v_mustInline_boxed_901_; lean_object* v_res_902_; 
v_mustInline_boxed_901_ = lean_unbox(v_mustInline_893_);
v_res_902_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_boxed_901_, v_code_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
return v_res_902_;
}
}
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object* v_s_903_, lean_object* v_code_904_, uint8_t v_mustInline_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_st_mk_ref(v_s_903_);
v___x_912_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_905_, v_code_904_, v___x_911_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_920_; 
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_920_ == 0)
{
lean_object* v_unused_921_; 
v_unused_921_ = lean_ctor_get(v___x_912_, 0);
lean_dec(v_unused_921_);
v___x_914_ = v___x_912_;
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
else
{
lean_dec(v___x_912_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_920_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_st_ref_get(v___x_911_);
lean_dec(v___x_911_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_916_);
v___x_918_ = v___x_914_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v___x_911_);
v_a_922_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_912_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_912_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_903_ = stack[0].m_obj;
lean_object* v_code_904_ = stack[1].m_obj;
uint8_t v_mustInline_905_ = stack[2].m_num;
lean_object* v_a_906_ = stack[3].m_obj;
lean_object* v_a_907_ = stack[4].m_obj;
lean_object* v_a_908_ = stack[5].m_obj;
lean_object* v_a_909_ = stack[6].m_obj;
lean_object* v_res_930_;
v_res_930_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_s_903_, v_code_904_, v_mustInline_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
stack->m_obj
 = v_res_930_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update___boxed(lean_object* v_s_931_, lean_object* v_code_932_, lean_object* v_mustInline_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
uint8_t v_mustInline_boxed_939_; lean_object* v_res_940_; 
v_mustInline_boxed_939_ = lean_unbox(v_mustInline_933_);
v_res_940_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_s_931_, v_code_932_, v_mustInline_boxed_939_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
return v_res_940_;
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

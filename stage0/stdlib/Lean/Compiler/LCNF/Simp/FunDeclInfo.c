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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* v_cellCount_118_; lean_object* v___x_119_; 
v_cellCount_118_ = lean_unsigned_to_nat(16u);
v___x_119_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_118_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1(void){
_start:
{
lean_object* v_cellCount_120_; lean_object* v___x_121_; 
v_cellCount_120_ = lean_unsigned_to_nat(16u);
v___x_121_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_120_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__2(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_122_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1, &l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__1);
v___x_123_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0, &l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__0);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
lean_ctor_set(v___x_125_, 2, v___x_122_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__2, &l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__2_once, _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default___closed__2);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap(void){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_Compiler_LCNF_Simp_instInhabitedFunDeclInfoMap_default;
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(lean_object* v_b_128_, lean_object* v_acc_129_, lean_object* v_i_130_){
_start:
{
lean_object* v_keyArray_135_; lean_object* v_valueArray_136_; lean_object* v___x_137_; uint8_t v___x_138_; 
v_keyArray_135_ = lean_ctor_get(v_b_128_, 1);
v_valueArray_136_ = lean_ctor_get(v_b_128_, 2);
v___x_137_ = lean_array_get_size(v_keyArray_135_);
v___x_138_ = lean_nat_dec_lt(v_i_130_, v___x_137_);
if (v___x_138_ == 0)
{
lean_dec(v_i_130_);
lean_inc(v_acc_129_);
return v_acc_129_;
}
else
{
lean_object* v___x_139_; uint8_t v_isSome_140_; 
v___x_139_ = lean_array_fget_borrowed(v_keyArray_135_, v_i_130_);
v_isSome_140_ = lean_noption_is_some(v___x_139_);
if (v_isSome_140_ == 0)
{
goto v___jp_131_;
}
else
{
lean_object* v___x_141_; uint8_t v_isSome_142_; 
v___x_141_ = lean_array_fget_borrowed(v_valueArray_136_, v_i_130_);
v_isSome_142_ = lean_noption_is_some(v___x_141_);
if (v_isSome_142_ == 0)
{
goto v___jp_131_;
}
else
{
lean_object* v_val_143_; lean_object* v_val_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
lean_inc(v___x_139_);
v_val_143_ = lean_noption_get(v___x_139_);
lean_inc(v___x_141_);
v_val_144_ = lean_noption_get(v___x_141_);
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = lean_nat_add(v_i_130_, v___x_145_);
lean_dec(v_i_130_);
v___x_147_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_b_128_, v_acc_129_, v___x_146_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v_val_143_);
lean_ctor_set(v___x_148_, 1, v_val_144_);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_147_);
return v___x_149_;
}
}
}
v___jp_131_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_i_130_, v___x_132_);
lean_dec(v_i_130_);
v_i_130_ = v___x_133_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0___boxed(lean_object* v_b_150_, lean_object* v_acc_151_, lean_object* v_i_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_b_150_, v_acc_151_, v_i_152_);
lean_dec(v_acc_151_);
lean_dec_ref(v_b_150_);
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
lean_object* v_result_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_result_209_ = lean_box(0);
v___x_210_ = lean_box(0);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__0(v_s_203_, v___x_210_, v___x_211_);
v___x_213_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v___x_212_, v_result_209_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format___boxed(lean_object* v_s_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(v_s_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec_ref(v_s_214_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(lean_object* v_as_221_, lean_object* v_as_x27_222_, lean_object* v_b_223_, lean_object* v_a_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___redArg(v_as_x27_222_, v_b_223_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1___boxed(lean_object* v_as_231_, lean_object* v_as_x27_232_, lean_object* v_b_233_, lean_object* v_a_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format_spec__1(v_as_231_, v_as_x27_232_, v_b_233_, v_a_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v_as_x27_232_);
lean_dec(v_as_231_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(lean_object* v_m_241_, lean_object* v_query_242_, lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v_zero_246_; uint8_t v_isZero_247_; 
v_zero_246_ = lean_unsigned_to_nat(0u);
v_isZero_247_ = lean_nat_dec_eq(v_x_244_, v_zero_246_);
if (v_isZero_247_ == 1)
{
lean_dec(v_x_245_);
lean_dec(v_x_244_);
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v___x_248_; 
v___x_248_ = lean_box(2);
return v___x_248_;
}
else
{
lean_object* v_val_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_val_249_ = lean_ctor_get(v_x_243_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v_x_243_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_val_249_);
lean_dec(v_x_243_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_val_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
lean_object* v_keyArray_257_; lean_object* v_valueArray_258_; lean_object* v___x_259_; uint8_t v_isSome_260_; 
v_keyArray_257_ = lean_ctor_get(v_m_241_, 1);
v_valueArray_258_ = lean_ctor_get(v_m_241_, 2);
v___x_259_ = lean_array_fget_borrowed(v_keyArray_257_, v_x_245_);
v_isSome_260_ = lean_noption_is_some(v___x_259_);
if (v_isSome_260_ == 0)
{
lean_dec(v_x_244_);
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v___x_261_; 
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_x_245_);
return v___x_261_;
}
else
{
lean_object* v_val_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v_x_245_);
v_val_262_ = lean_ctor_get(v_x_243_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v_x_243_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_val_262_);
lean_dec(v_x_243_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_val_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
else
{
lean_object* v_one_270_; lean_object* v_n_271_; lean_object* v___y_273_; 
v_one_270_ = lean_unsigned_to_nat(1u);
v_n_271_ = lean_nat_sub(v_x_244_, v_one_270_);
lean_dec(v_x_244_);
if (v_isSome_260_ == 0)
{
goto v___jp_279_;
}
else
{
lean_object* v___x_281_; uint8_t v_isSome_282_; 
v___x_281_ = lean_array_fget_borrowed(v_valueArray_258_, v_x_245_);
v_isSome_282_ = lean_noption_is_some(v___x_281_);
if (v_isSome_282_ == 0)
{
goto v___jp_279_;
}
else
{
lean_object* v_val_283_; uint8_t v___x_284_; 
lean_inc(v___x_259_);
v_val_283_ = lean_noption_get(v___x_259_);
v___x_284_ = l_Lean_instBEqFVarId_beq(v_val_283_, v_query_242_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
lean_dec(v_val_283_);
v___x_285_ = lean_array_get_size(v_keyArray_257_);
v___x_286_ = lean_nat_add(v_x_245_, v_one_270_);
lean_dec(v_x_245_);
v___x_287_ = lean_nat_dec_lt(v___x_286_, v___x_285_);
if (v___x_287_ == 0)
{
lean_dec(v___x_286_);
v_x_244_ = v_n_271_;
v_x_245_ = v_zero_246_;
goto _start;
}
else
{
v_x_244_ = v_n_271_;
v_x_245_ = v___x_286_;
goto _start;
}
}
else
{
lean_object* v_val_290_; lean_object* v___x_291_; 
lean_dec(v_n_271_);
lean_dec(v_x_243_);
lean_inc(v___x_281_);
v_val_290_ = lean_noption_get(v___x_281_);
v___x_291_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_291_, 0, v_x_245_);
lean_ctor_set(v___x_291_, 1, v_val_283_);
lean_ctor_set(v___x_291_, 2, v_val_290_);
return v___x_291_;
}
}
}
v___jp_272_:
{
lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_274_ = lean_array_get_size(v_keyArray_257_);
v___x_275_ = lean_nat_add(v_x_245_, v_one_270_);
lean_dec(v_x_245_);
v___x_276_ = lean_nat_dec_lt(v___x_275_, v___x_274_);
if (v___x_276_ == 0)
{
lean_dec(v___x_275_);
v_x_243_ = v___y_273_;
v_x_244_ = v_n_271_;
v_x_245_ = v_zero_246_;
goto _start;
}
else
{
v_x_243_ = v___y_273_;
v_x_244_ = v_n_271_;
v_x_245_ = v___x_275_;
goto _start;
}
}
v___jp_279_:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_object* v___x_280_; 
lean_inc(v_x_245_);
v___x_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_280_, 0, v_x_245_);
v___y_273_ = v___x_280_;
goto v___jp_272_;
}
else
{
v___y_273_ = v_x_243_;
goto v___jp_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg___boxed(lean_object* v_m_292_, lean_object* v_query_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_m_292_, v_query_293_, v_x_294_, v_x_295_, v_x_296_);
lean_dec(v_query_293_);
lean_dec_ref(v_m_292_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(lean_object* v_m_298_, lean_object* v_query_299_){
_start:
{
lean_object* v_keyArray_300_; lean_object* v___x_301_; uint64_t v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v_fold_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_keyArray_300_ = lean_ctor_get(v_m_298_, 1);
v___x_301_ = lean_array_get_size(v_keyArray_300_);
v___x_302_ = l_Lean_instHashableFVarId_hash(v_query_299_);
v___x_303_ = 32ULL;
v___x_304_ = lean_uint64_shift_right(v___x_302_, v___x_303_);
v_fold_305_ = lean_uint64_xor(v___x_302_, v___x_304_);
v___x_306_ = 16ULL;
v___x_307_ = lean_uint64_shift_right(v_fold_305_, v___x_306_);
v___x_308_ = lean_uint64_xor(v_fold_305_, v___x_307_);
v___x_309_ = lean_uint64_to_usize(v___x_308_);
v___x_310_ = lean_usize_of_nat(v___x_301_);
v___x_311_ = ((size_t)1ULL);
v___x_312_ = lean_usize_sub(v___x_310_, v___x_311_);
v___x_313_ = lean_usize_land(v___x_309_, v___x_312_);
v___x_314_ = lean_usize_to_nat(v___x_313_);
v___x_315_ = lean_box(0);
v___x_316_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_m_298_, v_query_299_, v___x_315_, v___x_301_, v___x_314_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg___boxed(lean_object* v_m_317_, lean_object* v_query_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_317_, v_query_318_);
lean_dec(v_query_318_);
lean_dec_ref(v_m_317_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___redArg(lean_object* v_b_320_, lean_object* v_acc_321_, lean_object* v_i_322_){
_start:
{
lean_object* v___y_324_; lean_object* v_keyArray_332_; lean_object* v_valueArray_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_keyArray_332_ = lean_ctor_get(v_b_320_, 1);
v_valueArray_333_ = lean_ctor_get(v_b_320_, 2);
v___x_334_ = lean_array_get_size(v_keyArray_332_);
v___x_335_ = lean_nat_dec_lt(v_i_322_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec(v_i_322_);
return v_acc_321_;
}
else
{
lean_object* v___x_336_; uint8_t v_isSome_337_; 
v___x_336_ = lean_array_fget_borrowed(v_keyArray_332_, v_i_322_);
v_isSome_337_ = lean_noption_is_some(v___x_336_);
if (v_isSome_337_ == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v___x_338_; uint8_t v_isSome_339_; 
v___x_338_ = lean_array_fget_borrowed(v_valueArray_333_, v_i_322_);
v_isSome_339_ = lean_noption_is_some(v___x_338_);
if (v_isSome_339_ == 0)
{
goto v___jp_328_;
}
else
{
lean_object* v_val_340_; lean_object* v_val_341_; lean_object* v_i_343_; lean_object* v___x_348_; 
lean_inc(v___x_336_);
v_val_340_ = lean_noption_get(v___x_336_);
lean_inc(v___x_338_);
v_val_341_ = lean_noption_get(v___x_338_);
v___x_348_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_acc_321_, v_val_340_);
switch(lean_obj_tag(v___x_348_))
{
case 0:
{
lean_object* v_index_349_; lean_object* v_size_350_; lean_object* v___x_351_; 
v_index_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_index_349_);
lean_dec_ref_known(v___x_348_, 3);
v_size_350_ = lean_ctor_get(v_acc_321_, 0);
lean_inc(v_size_350_);
v___x_351_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_321_, v_size_350_, v_index_349_, v_val_340_, v_val_341_);
lean_dec(v_index_349_);
v___y_324_ = v___x_351_;
goto v___jp_323_;
}
case 1:
{
lean_object* v_index_352_; 
v_index_352_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_index_352_);
lean_dec_ref_known(v___x_348_, 1);
v_i_343_ = v_index_352_;
goto v___jp_342_;
}
default: 
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_321_, v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_index_355_; 
v_index_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_index_355_);
lean_dec_ref_known(v___x_354_, 1);
v_i_343_ = v_index_355_;
goto v___jp_342_;
}
else
{
lean_dec(v_val_341_);
lean_dec(v_val_340_);
v___y_324_ = v_acc_321_;
goto v___jp_323_;
}
}
}
v___jp_342_:
{
lean_object* v_size_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_size_344_ = lean_ctor_get(v_acc_321_, 0);
v___x_345_ = lean_unsigned_to_nat(1u);
v___x_346_ = lean_nat_add(v_size_344_, v___x_345_);
v___x_347_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_321_, v___x_346_, v_i_343_, v_val_340_, v_val_341_);
lean_dec(v_i_343_);
v___y_324_ = v___x_347_;
goto v___jp_323_;
}
}
}
}
v___jp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_i_322_, v___x_325_);
lean_dec(v_i_322_);
v_acc_321_ = v___y_324_;
v_i_322_ = v___x_326_;
goto _start;
}
v___jp_328_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(1u);
v___x_330_ = lean_nat_add(v_i_322_, v___x_329_);
lean_dec(v_i_322_);
v_i_322_ = v___x_330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_356_, lean_object* v_acc_357_, lean_object* v_i_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___redArg(v_b_356_, v_acc_357_, v_i_358_);
lean_dec_ref(v_b_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___redArg(lean_object* v_init_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___redArg(v_b_361_, v_init_360_, v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___redArg___boxed(lean_object* v_init_364_, lean_object* v_b_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___redArg(v_init_364_, v_b_365_);
lean_dec_ref(v_b_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(lean_object* v_m_367_){
_start:
{
lean_object* v_keyArray_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_cellCount_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v_target_375_; lean_object* v___x_376_; 
v_keyArray_368_ = lean_ctor_get(v_m_367_, 1);
v___x_369_ = lean_array_get_size(v_keyArray_368_);
v___x_370_ = lean_unsigned_to_nat(2u);
v_cellCount_371_ = lean_nat_mul(v___x_369_, v___x_370_);
v___x_372_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_371_);
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_371_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_371_);
v_target_375_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_375_, 0, v___x_372_);
lean_ctor_set(v_target_375_, 1, v___x_373_);
lean_ctor_set(v_target_375_, 2, v___x_374_);
v___x_376_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___redArg(v_target_375_, v_m_367_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg___boxed(lean_object* v_m_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_m_377_);
lean_dec_ref(v_m_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(lean_object* v_m_379_, lean_object* v_query_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_379_, v_query_380_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_index_382_; lean_object* v_key_383_; lean_object* v_value_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_index_382_ = lean_ctor_get(v___x_381_, 0);
v_key_383_ = lean_ctor_get(v___x_381_, 1);
v_value_384_ = lean_ctor_get(v___x_381_, 2);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_381_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_value_384_);
lean_inc(v_key_383_);
lean_inc(v_index_382_);
lean_dec(v___x_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_index_382_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_key_383_);
lean_ctor_set(v_reuseFailAlloc_390_, 2, v_value_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v___x_381_);
v___x_392_ = lean_box(1);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg___boxed(lean_object* v_m_393_, lean_object* v_query_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_m_393_, v_query_394_);
lean_dec(v_query_394_);
lean_dec_ref(v_m_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(lean_object* v_m_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_m_396_, v_a_397_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_value_399_; lean_object* v___x_400_; 
v_value_399_ = lean_ctor_get(v___x_398_, 2);
lean_inc(v_value_399_);
lean_dec_ref_known(v___x_398_, 3);
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_value_399_);
return v___x_400_;
}
else
{
lean_object* v___x_401_; 
v___x_401_ = lean_box(0);
return v___x_401_;
}
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
uint8_t v___x_408_; lean_object* v___y_410_; lean_object* v_i_411_; lean_object* v___y_418_; lean_object* v___y_429_; lean_object* v_i_430_; lean_object* v___x_447_; 
v___x_408_ = 0;
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_405_, v_fvarId_406_);
switch(lean_obj_tag(v___x_447_))
{
case 0:
{
lean_object* v_index_448_; lean_object* v_size_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_index_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_index_448_);
lean_dec_ref_known(v___x_447_, 3);
v_size_449_ = lean_ctor_get(v_s_405_, 0);
lean_inc(v_size_449_);
v___x_450_ = lean_box(v___x_408_);
v___x_451_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_405_, v_size_449_, v_index_448_, v_fvarId_406_, v___x_450_);
lean_dec(v_index_448_);
return v___x_451_;
}
case 1:
{
lean_object* v_index_452_; lean_object* v_size_453_; lean_object* v_keyArray_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_index_452_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_index_452_);
lean_dec_ref_known(v___x_447_, 1);
v_size_453_ = lean_ctor_get(v_s_405_, 0);
v_keyArray_454_ = lean_ctor_get(v_s_405_, 1);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v_size_453_, v___x_455_);
v___x_457_ = lean_array_get_size(v_keyArray_454_);
v___x_458_ = lean_nat_dec_lt(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_dec(v___x_456_);
lean_dec(v_index_452_);
goto v___jp_436_;
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_459_ = lean_unsigned_to_nat(4u);
v___x_460_ = lean_nat_mul(v___x_456_, v___x_459_);
v___x_461_ = lean_unsigned_to_nat(3u);
v___x_462_ = lean_nat_mul(v___x_457_, v___x_461_);
v___x_463_ = lean_nat_dec_le(v___x_460_, v___x_462_);
lean_dec(v___x_462_);
lean_dec(v___x_460_);
if (v___x_463_ == 0)
{
lean_dec(v___x_456_);
lean_dec(v_index_452_);
goto v___jp_436_;
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = lean_box(v___x_408_);
v___x_465_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_405_, v___x_456_, v_index_452_, v_fvarId_406_, v___x_464_);
lean_dec(v_index_452_);
return v___x_465_;
}
}
}
default: 
{
lean_object* v_size_466_; lean_object* v_keyArray_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v_size_466_ = lean_ctor_get(v_s_405_, 0);
v_keyArray_467_ = lean_ctor_get(v_s_405_, 1);
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_size_466_, v___x_468_);
v___x_470_ = lean_array_get_size(v_keyArray_467_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; 
lean_dec(v___x_469_);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_405_);
lean_dec_ref(v_s_405_);
v___y_418_ = v___x_472_;
goto v___jp_417_;
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_473_ = lean_unsigned_to_nat(4u);
v___x_474_ = lean_nat_mul(v___x_469_, v___x_473_);
lean_dec(v___x_469_);
v___x_475_ = lean_unsigned_to_nat(3u);
v___x_476_ = lean_nat_mul(v___x_470_, v___x_475_);
v___x_477_ = lean_nat_dec_le(v___x_474_, v___x_476_);
lean_dec(v___x_476_);
lean_dec(v___x_474_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_405_);
lean_dec_ref(v_s_405_);
v___y_418_ = v___x_478_;
goto v___jp_417_;
}
else
{
v___y_418_ = v_s_405_;
goto v___jp_417_;
}
}
}
}
v___jp_409_:
{
lean_object* v_size_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_size_412_ = lean_ctor_get(v___y_410_, 0);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_add(v_size_412_, v___x_413_);
v___x_415_ = lean_box(v___x_408_);
v___x_416_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_410_, v___x_414_, v_i_411_, v_fvarId_406_, v___x_415_);
lean_dec(v_i_411_);
return v___x_416_;
}
v___jp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___y_418_, v_fvarId_406_);
switch(lean_obj_tag(v___x_419_))
{
case 0:
{
lean_object* v_index_420_; lean_object* v_size_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_index_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_index_420_);
lean_dec_ref_known(v___x_419_, 3);
v_size_421_ = lean_ctor_get(v___y_418_, 0);
lean_inc(v_size_421_);
v___x_422_ = lean_box(v___x_408_);
v___x_423_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_418_, v_size_421_, v_index_420_, v_fvarId_406_, v___x_422_);
lean_dec(v_index_420_);
return v___x_423_;
}
case 1:
{
lean_object* v_index_424_; 
v_index_424_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_index_424_);
lean_dec_ref_known(v___x_419_, 1);
v___y_410_ = v___y_418_;
v_i_411_ = v_index_424_;
goto v___jp_409_;
}
default: 
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_418_, v___x_425_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_index_427_; 
v_index_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_index_427_);
lean_dec_ref_known(v___x_426_, 1);
v___y_410_ = v___y_418_;
v_i_411_ = v_index_427_;
goto v___jp_409_;
}
else
{
lean_dec(v_fvarId_406_);
return v___y_418_;
}
}
}
}
v___jp_428_:
{
lean_object* v_size_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_size_431_ = lean_ctor_get(v___y_429_, 0);
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = lean_nat_add(v_size_431_, v___x_432_);
v___x_434_ = lean_box(v___x_408_);
v___x_435_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_429_, v___x_433_, v_i_430_, v_fvarId_406_, v___x_434_);
lean_dec(v_i_430_);
return v___x_435_;
}
v___jp_436_:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_405_);
lean_dec_ref(v_s_405_);
v___x_438_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___x_437_, v_fvarId_406_);
switch(lean_obj_tag(v___x_438_))
{
case 0:
{
lean_object* v_index_439_; lean_object* v_size_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v_index_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_index_439_);
lean_dec_ref_known(v___x_438_, 3);
v_size_440_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_size_440_);
v___x_441_ = lean_box(v___x_408_);
v___x_442_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_437_, v_size_440_, v_index_439_, v_fvarId_406_, v___x_441_);
lean_dec(v_index_439_);
return v___x_442_;
}
case 1:
{
lean_object* v_index_443_; 
v_index_443_ = lean_ctor_get(v___x_438_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_438_, 1);
v___y_429_ = v___x_437_;
v_i_430_ = v_index_443_;
goto v___jp_428_;
}
default: 
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_437_, v___x_444_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_index_446_; 
v_index_446_ = lean_ctor_get(v___x_445_, 0);
lean_inc(v_index_446_);
lean_dec_ref_known(v___x_445_, 1);
v___y_429_ = v___x_437_;
v_i_430_ = v_index_446_;
goto v___jp_428_;
}
else
{
lean_dec(v_fvarId_406_);
return v___x_437_;
}
}
}
}
}
else
{
lean_object* v_val_479_; uint8_t v___x_480_; 
v_val_479_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_val_479_);
lean_dec_ref_known(v___x_407_, 1);
v___x_480_ = lean_unbox(v_val_479_);
lean_dec(v_val_479_);
if (v___x_480_ == 0)
{
uint8_t v___x_481_; lean_object* v___y_483_; lean_object* v_i_484_; lean_object* v___y_491_; lean_object* v___y_502_; lean_object* v_i_503_; lean_object* v___x_520_; 
v___x_481_ = 1;
v___x_520_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_405_, v_fvarId_406_);
switch(lean_obj_tag(v___x_520_))
{
case 0:
{
lean_object* v_index_521_; lean_object* v_size_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_index_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_521_);
lean_dec_ref_known(v___x_520_, 3);
v_size_522_ = lean_ctor_get(v_s_405_, 0);
lean_inc(v_size_522_);
v___x_523_ = lean_box(v___x_481_);
v___x_524_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_405_, v_size_522_, v_index_521_, v_fvarId_406_, v___x_523_);
lean_dec(v_index_521_);
return v___x_524_;
}
case 1:
{
lean_object* v_index_525_; lean_object* v_size_526_; lean_object* v_keyArray_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_index_525_ = lean_ctor_get(v___x_520_, 0);
lean_inc(v_index_525_);
lean_dec_ref_known(v___x_520_, 1);
v_size_526_ = lean_ctor_get(v_s_405_, 0);
v_keyArray_527_ = lean_ctor_get(v_s_405_, 1);
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_size_526_, v___x_528_);
v___x_530_ = lean_array_get_size(v_keyArray_527_);
v___x_531_ = lean_nat_dec_lt(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_dec(v___x_529_);
lean_dec(v_index_525_);
goto v___jp_509_;
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_532_ = lean_unsigned_to_nat(4u);
v___x_533_ = lean_nat_mul(v___x_529_, v___x_532_);
v___x_534_ = lean_unsigned_to_nat(3u);
v___x_535_ = lean_nat_mul(v___x_530_, v___x_534_);
v___x_536_ = lean_nat_dec_le(v___x_533_, v___x_535_);
lean_dec(v___x_535_);
lean_dec(v___x_533_);
if (v___x_536_ == 0)
{
lean_dec(v___x_529_);
lean_dec(v_index_525_);
goto v___jp_509_;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = lean_box(v___x_481_);
v___x_538_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_405_, v___x_529_, v_index_525_, v_fvarId_406_, v___x_537_);
lean_dec(v_index_525_);
return v___x_538_;
}
}
}
default: 
{
lean_object* v_size_539_; lean_object* v_keyArray_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_size_539_ = lean_ctor_get(v_s_405_, 0);
v_keyArray_540_ = lean_ctor_get(v_s_405_, 1);
v___x_541_ = lean_unsigned_to_nat(1u);
v___x_542_ = lean_nat_add(v_size_539_, v___x_541_);
v___x_543_ = lean_array_get_size(v_keyArray_540_);
v___x_544_ = lean_nat_dec_lt(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
lean_dec(v___x_542_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_405_);
lean_dec_ref(v_s_405_);
v___y_491_ = v___x_545_;
goto v___jp_490_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_546_ = lean_unsigned_to_nat(4u);
v___x_547_ = lean_nat_mul(v___x_542_, v___x_546_);
lean_dec(v___x_542_);
v___x_548_ = lean_unsigned_to_nat(3u);
v___x_549_ = lean_nat_mul(v___x_543_, v___x_548_);
v___x_550_ = lean_nat_dec_le(v___x_547_, v___x_549_);
lean_dec(v___x_549_);
lean_dec(v___x_547_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_405_);
lean_dec_ref(v_s_405_);
v___y_491_ = v___x_551_;
goto v___jp_490_;
}
else
{
v___y_491_ = v_s_405_;
goto v___jp_490_;
}
}
}
}
v___jp_482_:
{
lean_object* v_size_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v_size_485_ = lean_ctor_get(v___y_483_, 0);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_size_485_, v___x_486_);
v___x_488_ = lean_box(v___x_481_);
v___x_489_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_483_, v___x_487_, v_i_484_, v_fvarId_406_, v___x_488_);
lean_dec(v_i_484_);
return v___x_489_;
}
v___jp_490_:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___y_491_, v_fvarId_406_);
switch(lean_obj_tag(v___x_492_))
{
case 0:
{
lean_object* v_index_493_; lean_object* v_size_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v_index_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_index_493_);
lean_dec_ref_known(v___x_492_, 3);
v_size_494_ = lean_ctor_get(v___y_491_, 0);
lean_inc(v_size_494_);
v___x_495_ = lean_box(v___x_481_);
v___x_496_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_491_, v_size_494_, v_index_493_, v_fvarId_406_, v___x_495_);
lean_dec(v_index_493_);
return v___x_496_;
}
case 1:
{
lean_object* v_index_497_; 
v_index_497_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_index_497_);
lean_dec_ref_known(v___x_492_, 1);
v___y_483_ = v___y_491_;
v_i_484_ = v_index_497_;
goto v___jp_482_;
}
default: 
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_491_, v___x_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_index_500_; 
v_index_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_index_500_);
lean_dec_ref_known(v___x_499_, 1);
v___y_483_ = v___y_491_;
v_i_484_ = v_index_500_;
goto v___jp_482_;
}
else
{
lean_dec(v_fvarId_406_);
return v___y_491_;
}
}
}
}
v___jp_501_:
{
lean_object* v_size_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_size_504_ = lean_ctor_get(v___y_502_, 0);
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v_size_504_, v___x_505_);
v___x_507_ = lean_box(v___x_481_);
v___x_508_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_502_, v___x_506_, v_i_503_, v_fvarId_406_, v___x_507_);
lean_dec(v_i_503_);
return v___x_508_;
}
v___jp_509_:
{
lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_405_);
lean_dec_ref(v_s_405_);
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___x_510_, v_fvarId_406_);
switch(lean_obj_tag(v___x_511_))
{
case 0:
{
lean_object* v_index_512_; lean_object* v_size_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v_index_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_index_512_);
lean_dec_ref_known(v___x_511_, 3);
v_size_513_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_size_513_);
v___x_514_ = lean_box(v___x_481_);
v___x_515_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_510_, v_size_513_, v_index_512_, v_fvarId_406_, v___x_514_);
lean_dec(v_index_512_);
return v___x_515_;
}
case 1:
{
lean_object* v_index_516_; 
v_index_516_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_index_516_);
lean_dec_ref_known(v___x_511_, 1);
v___y_502_ = v___x_510_;
v_i_503_ = v_index_516_;
goto v___jp_501_;
}
default: 
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_510_, v___x_517_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_index_519_; 
v_index_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_index_519_);
lean_dec_ref_known(v___x_518_, 1);
v___y_502_ = v___x_510_;
v_i_503_ = v_index_519_;
goto v___jp_501_;
}
else
{
lean_dec(v_fvarId_406_);
return v___x_510_;
}
}
}
}
}
else
{
lean_dec(v_fvarId_406_);
return v_s_405_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(lean_object* v_00_u03b2_552_, lean_object* v_m_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_m_553_, v_a_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___boxed(lean_object* v_00_u03b2_556_, lean_object* v_m_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0(v_00_u03b2_556_, v_m_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_m_557_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(lean_object* v_00_u03b2_560_, lean_object* v_m_561_, lean_object* v_query_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_m_561_, v_query_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___boxed(lean_object* v_00_u03b2_564_, lean_object* v_m_565_, lean_object* v_query_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1(v_00_u03b2_564_, v_m_565_, v_query_566_);
lean_dec(v_query_566_);
lean_dec_ref(v_m_565_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2(lean_object* v_00_u03b2_568_, lean_object* v_m_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_m_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___boxed(lean_object* v_00_u03b2_571_, lean_object* v_m_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2(v_00_u03b2_571_, v_m_572_);
lean_dec_ref(v_m_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_query_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_m_575_, v_query_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___boxed(lean_object* v_00_u03b2_578_, lean_object* v_m_579_, lean_object* v_query_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0(v_00_u03b2_578_, v_m_579_, v_query_580_);
lean_dec(v_query_580_);
lean_dec_ref(v_m_579_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(lean_object* v_00_u03b2_582_, lean_object* v_m_583_, lean_object* v_query_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___redArg(v_m_583_, v_query_584_, v_x_585_, v_x_586_, v_x_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2___boxed(lean_object* v_00_u03b2_590_, lean_object* v_m_591_, lean_object* v_query_592_, lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1_spec__2(v_00_u03b2_590_, v_m_591_, v_query_592_, v_x_593_, v_x_594_, v_x_595_, v_x_596_);
lean_dec(v_query_592_);
lean_dec_ref(v_m_591_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4(lean_object* v_00_u03b2_598_, lean_object* v_init_599_, lean_object* v_b_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___redArg(v_init_599_, v_b_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4___boxed(lean_object* v_00_u03b2_602_, lean_object* v_init_603_, lean_object* v_b_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4(v_00_u03b2_602_, v_init_603_, v_b_604_);
lean_dec_ref(v_b_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_606_, lean_object* v_b_607_, lean_object* v_acc_608_, lean_object* v_i_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___redArg(v_b_607_, v_acc_608_, v_i_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_611_, lean_object* v_b_612_, lean_object* v_acc_613_, lean_object* v_i_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2_spec__4_spec__5(v_00_u03b2_611_, v_b_612_, v_acc_613_, v_i_614_);
lean_dec_ref(v_b_612_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(lean_object* v_s_616_, lean_object* v_fvarId_617_){
_start:
{
uint8_t v___y_619_; lean_object* v___y_620_; lean_object* v_i_621_; uint8_t v___y_628_; lean_object* v___y_629_; uint8_t v___y_640_; lean_object* v___y_641_; lean_object* v_i_642_; uint8_t v___y_649_; lean_object* v___x_694_; 
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0___redArg(v_s_616_, v_fvarId_617_);
if (lean_obj_tag(v___x_694_) == 0)
{
goto v___jp_660_;
}
else
{
lean_object* v_val_695_; uint8_t v___x_696_; 
v_val_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_val_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = lean_unbox(v_val_695_);
lean_dec(v_val_695_);
if (v___x_696_ == 0)
{
goto v___jp_660_;
}
else
{
lean_dec(v_fvarId_617_);
return v_s_616_;
}
}
v___jp_618_:
{
lean_object* v_size_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_size_622_ = lean_ctor_get(v___y_620_, 0);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v_size_622_, v___x_623_);
v___x_625_ = lean_box(v___y_619_);
v___x_626_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_620_, v___x_624_, v_i_621_, v_fvarId_617_, v___x_625_);
lean_dec(v_i_621_);
return v___x_626_;
}
v___jp_627_:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___y_629_, v_fvarId_617_);
switch(lean_obj_tag(v___x_630_))
{
case 0:
{
lean_object* v_index_631_; lean_object* v_size_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_index_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_index_631_);
lean_dec_ref_known(v___x_630_, 3);
v_size_632_ = lean_ctor_get(v___y_629_, 0);
lean_inc(v_size_632_);
v___x_633_ = lean_box(v___y_628_);
v___x_634_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_629_, v_size_632_, v_index_631_, v_fvarId_617_, v___x_633_);
lean_dec(v_index_631_);
return v___x_634_;
}
case 1:
{
lean_object* v_index_635_; 
v_index_635_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_index_635_);
lean_dec_ref_known(v___x_630_, 1);
v___y_619_ = v___y_628_;
v___y_620_ = v___y_629_;
v_i_621_ = v_index_635_;
goto v___jp_618_;
}
default: 
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_unsigned_to_nat(0u);
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_629_, v___x_636_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_index_638_; 
v_index_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_index_638_);
lean_dec_ref_known(v___x_637_, 1);
v___y_619_ = v___y_628_;
v___y_620_ = v___y_629_;
v_i_621_ = v_index_638_;
goto v___jp_618_;
}
else
{
lean_dec(v_fvarId_617_);
return v___y_629_;
}
}
}
}
v___jp_639_:
{
lean_object* v_size_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_size_643_ = lean_ctor_get(v___y_641_, 0);
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = lean_nat_add(v_size_643_, v___x_644_);
v___x_646_ = lean_box(v___y_640_);
v___x_647_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_641_, v___x_645_, v_i_642_, v_fvarId_617_, v___x_646_);
lean_dec(v_i_642_);
return v___x_647_;
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_616_);
lean_dec_ref(v_s_616_);
v___x_651_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___x_650_, v_fvarId_617_);
switch(lean_obj_tag(v___x_651_))
{
case 0:
{
lean_object* v_index_652_; lean_object* v_size_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_index_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_index_652_);
lean_dec_ref_known(v___x_651_, 3);
v_size_653_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_size_653_);
v___x_654_ = lean_box(v___y_649_);
v___x_655_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_650_, v_size_653_, v_index_652_, v_fvarId_617_, v___x_654_);
lean_dec(v_index_652_);
return v___x_655_;
}
case 1:
{
lean_object* v_index_656_; 
v_index_656_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_index_656_);
lean_dec_ref_known(v___x_651_, 1);
v___y_640_ = v___y_649_;
v___y_641_ = v___x_650_;
v_i_642_ = v_index_656_;
goto v___jp_639_;
}
default: 
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_650_, v___x_657_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_index_659_; 
v_index_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_index_659_);
lean_dec_ref_known(v___x_658_, 1);
v___y_640_ = v___y_649_;
v___y_641_ = v___x_650_;
v_i_642_ = v_index_659_;
goto v___jp_639_;
}
else
{
lean_dec(v_fvarId_617_);
return v___x_650_;
}
}
}
}
v___jp_660_:
{
uint8_t v___x_661_; lean_object* v___x_662_; 
v___x_661_ = 1;
v___x_662_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_616_, v_fvarId_617_);
switch(lean_obj_tag(v___x_662_))
{
case 0:
{
lean_object* v_index_663_; lean_object* v_size_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_index_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_index_663_);
lean_dec_ref_known(v___x_662_, 3);
v_size_664_ = lean_ctor_get(v_s_616_, 0);
lean_inc(v_size_664_);
v___x_665_ = lean_box(v___x_661_);
v___x_666_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_616_, v_size_664_, v_index_663_, v_fvarId_617_, v___x_665_);
lean_dec(v_index_663_);
return v___x_666_;
}
case 1:
{
lean_object* v_index_667_; lean_object* v_size_668_; lean_object* v_keyArray_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_index_667_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_index_667_);
lean_dec_ref_known(v___x_662_, 1);
v_size_668_ = lean_ctor_get(v_s_616_, 0);
v_keyArray_669_ = lean_ctor_get(v_s_616_, 1);
v___x_670_ = lean_unsigned_to_nat(1u);
v___x_671_ = lean_nat_add(v_size_668_, v___x_670_);
v___x_672_ = lean_array_get_size(v_keyArray_669_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec(v___x_671_);
lean_dec(v_index_667_);
v___y_649_ = v___x_661_;
goto v___jp_648_;
}
else
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_674_ = lean_unsigned_to_nat(4u);
v___x_675_ = lean_nat_mul(v___x_671_, v___x_674_);
v___x_676_ = lean_unsigned_to_nat(3u);
v___x_677_ = lean_nat_mul(v___x_672_, v___x_676_);
v___x_678_ = lean_nat_dec_le(v___x_675_, v___x_677_);
lean_dec(v___x_677_);
lean_dec(v___x_675_);
if (v___x_678_ == 0)
{
lean_dec(v___x_671_);
lean_dec(v_index_667_);
v___y_649_ = v___x_661_;
goto v___jp_648_;
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; 
v___x_679_ = lean_box(v___x_661_);
v___x_680_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_616_, v___x_671_, v_index_667_, v_fvarId_617_, v___x_679_);
lean_dec(v_index_667_);
return v___x_680_;
}
}
}
default: 
{
lean_object* v_size_681_; lean_object* v_keyArray_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_size_681_ = lean_ctor_get(v_s_616_, 0);
v_keyArray_682_ = lean_ctor_get(v_s_616_, 1);
v___x_683_ = lean_unsigned_to_nat(1u);
v___x_684_ = lean_nat_add(v_size_681_, v___x_683_);
v___x_685_ = lean_array_get_size(v_keyArray_682_);
v___x_686_ = lean_nat_dec_lt(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; 
lean_dec(v___x_684_);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_616_);
lean_dec_ref(v_s_616_);
v___y_628_ = v___x_661_;
v___y_629_ = v___x_687_;
goto v___jp_627_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_688_ = lean_unsigned_to_nat(4u);
v___x_689_ = lean_nat_mul(v___x_684_, v___x_688_);
lean_dec(v___x_684_);
v___x_690_ = lean_unsigned_to_nat(3u);
v___x_691_ = lean_nat_mul(v___x_685_, v___x_690_);
v___x_692_ = lean_nat_dec_le(v___x_689_, v___x_691_);
lean_dec(v___x_691_);
lean_dec(v___x_689_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_616_);
lean_dec_ref(v_s_616_);
v___y_628_ = v___x_661_;
v___y_629_ = v___x_693_;
goto v___jp_627_;
}
else
{
v___y_628_ = v___x_661_;
v___y_629_ = v_s_616_;
goto v___jp_627_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(lean_object* v_s_697_, lean_object* v_fvarId_698_){
_start:
{
uint8_t v___x_699_; lean_object* v___y_701_; lean_object* v_i_702_; lean_object* v___y_709_; lean_object* v___y_720_; lean_object* v_i_721_; lean_object* v___x_738_; 
v___x_699_ = 2;
v___x_738_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_697_, v_fvarId_698_);
switch(lean_obj_tag(v___x_738_))
{
case 0:
{
lean_object* v_index_739_; lean_object* v_size_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_index_739_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_index_739_);
lean_dec_ref_known(v___x_738_, 3);
v_size_740_ = lean_ctor_get(v_s_697_, 0);
lean_inc(v_size_740_);
v___x_741_ = lean_box(v___x_699_);
v___x_742_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_697_, v_size_740_, v_index_739_, v_fvarId_698_, v___x_741_);
lean_dec(v_index_739_);
return v___x_742_;
}
case 1:
{
lean_object* v_index_743_; lean_object* v_size_744_; lean_object* v_keyArray_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_index_743_ = lean_ctor_get(v___x_738_, 0);
lean_inc(v_index_743_);
lean_dec_ref_known(v___x_738_, 1);
v_size_744_ = lean_ctor_get(v_s_697_, 0);
v_keyArray_745_ = lean_ctor_get(v_s_697_, 1);
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = lean_nat_add(v_size_744_, v___x_746_);
v___x_748_ = lean_array_get_size(v_keyArray_745_);
v___x_749_ = lean_nat_dec_lt(v___x_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec(v___x_747_);
lean_dec(v_index_743_);
goto v___jp_727_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_750_ = lean_unsigned_to_nat(4u);
v___x_751_ = lean_nat_mul(v___x_747_, v___x_750_);
v___x_752_ = lean_unsigned_to_nat(3u);
v___x_753_ = lean_nat_mul(v___x_748_, v___x_752_);
v___x_754_ = lean_nat_dec_le(v___x_751_, v___x_753_);
lean_dec(v___x_753_);
lean_dec(v___x_751_);
if (v___x_754_ == 0)
{
lean_dec(v___x_747_);
lean_dec(v_index_743_);
goto v___jp_727_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_box(v___x_699_);
v___x_756_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_697_, v___x_747_, v_index_743_, v_fvarId_698_, v___x_755_);
lean_dec(v_index_743_);
return v___x_756_;
}
}
}
default: 
{
lean_object* v_size_757_; lean_object* v_keyArray_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_size_757_ = lean_ctor_get(v_s_697_, 0);
v_keyArray_758_ = lean_ctor_get(v_s_697_, 1);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_add(v_size_757_, v___x_759_);
v___x_761_ = lean_array_get_size(v_keyArray_758_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_dec(v___x_760_);
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_697_);
lean_dec_ref(v_s_697_);
v___y_709_ = v___x_763_;
goto v___jp_708_;
}
else
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_764_ = lean_unsigned_to_nat(4u);
v___x_765_ = lean_nat_mul(v___x_760_, v___x_764_);
lean_dec(v___x_760_);
v___x_766_ = lean_unsigned_to_nat(3u);
v___x_767_ = lean_nat_mul(v___x_761_, v___x_766_);
v___x_768_ = lean_nat_dec_le(v___x_765_, v___x_767_);
lean_dec(v___x_767_);
lean_dec(v___x_765_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_697_);
lean_dec_ref(v_s_697_);
v___y_709_ = v___x_769_;
goto v___jp_708_;
}
else
{
v___y_709_ = v_s_697_;
goto v___jp_708_;
}
}
}
}
v___jp_700_:
{
lean_object* v_size_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_size_703_ = lean_ctor_get(v___y_701_, 0);
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_size_703_, v___x_704_);
v___x_706_ = lean_box(v___x_699_);
v___x_707_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_701_, v___x_705_, v_i_702_, v_fvarId_698_, v___x_706_);
lean_dec(v_i_702_);
return v___x_707_;
}
v___jp_708_:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___y_709_, v_fvarId_698_);
switch(lean_obj_tag(v___x_710_))
{
case 0:
{
lean_object* v_index_711_; lean_object* v_size_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_index_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_index_711_);
lean_dec_ref_known(v___x_710_, 3);
v_size_712_ = lean_ctor_get(v___y_709_, 0);
lean_inc(v_size_712_);
v___x_713_ = lean_box(v___x_699_);
v___x_714_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_709_, v_size_712_, v_index_711_, v_fvarId_698_, v___x_713_);
lean_dec(v_index_711_);
return v___x_714_;
}
case 1:
{
lean_object* v_index_715_; 
v_index_715_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_index_715_);
lean_dec_ref_known(v___x_710_, 1);
v___y_701_ = v___y_709_;
v_i_702_ = v_index_715_;
goto v___jp_700_;
}
default: 
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_unsigned_to_nat(0u);
v___x_717_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_709_, v___x_716_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_index_718_; 
v_index_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_index_718_);
lean_dec_ref_known(v___x_717_, 1);
v___y_701_ = v___y_709_;
v_i_702_ = v_index_718_;
goto v___jp_700_;
}
else
{
lean_dec(v_fvarId_698_);
return v___y_709_;
}
}
}
}
v___jp_719_:
{
lean_object* v_size_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_size_722_ = lean_ctor_get(v___y_720_, 0);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_add(v_size_722_, v___x_723_);
v___x_725_ = lean_box(v___x_699_);
v___x_726_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_720_, v___x_724_, v_i_721_, v_fvarId_698_, v___x_725_);
lean_dec(v_i_721_);
return v___x_726_;
}
v___jp_727_:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_697_);
lean_dec_ref(v_s_697_);
v___x_729_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___x_728_, v_fvarId_698_);
switch(lean_obj_tag(v___x_729_))
{
case 0:
{
lean_object* v_index_730_; lean_object* v_size_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_index_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_index_730_);
lean_dec_ref_known(v___x_729_, 3);
v_size_731_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_size_731_);
v___x_732_ = lean_box(v___x_699_);
v___x_733_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_728_, v_size_731_, v_index_730_, v_fvarId_698_, v___x_732_);
lean_dec(v_index_730_);
return v___x_733_;
}
case 1:
{
lean_object* v_index_734_; 
v_index_734_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_index_734_);
lean_dec_ref_known(v___x_729_, 1);
v___y_720_ = v___x_728_;
v_i_721_ = v_index_734_;
goto v___jp_719_;
}
default: 
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_unsigned_to_nat(0u);
v___x_736_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_728_, v___x_735_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_index_737_; 
v_index_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_index_737_);
lean_dec_ref_known(v___x_736_, 1);
v___y_720_ = v___x_728_;
v_i_721_ = v_index_737_;
goto v___jp_719_;
}
else
{
lean_dec(v_fvarId_698_);
return v___x_728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__0_spec__0___redArg(v_m_770_, v_a_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
lean_object* v_index_773_; lean_object* v_size_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v_index_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc(v_index_773_);
lean_dec_ref_known(v___x_772_, 3);
v_size_774_ = lean_ctor_get(v_m_770_, 0);
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_sub(v_size_774_, v___x_775_);
v___x_777_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_770_, v___x_776_, v_index_773_);
lean_dec(v_index_773_);
return v___x_777_;
}
else
{
return v_m_770_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg___boxed(lean_object* v_m_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_778_, v_a_779_);
lean_dec(v_a_779_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore(lean_object* v_s_781_, lean_object* v_fvarId_782_, lean_object* v_saved_x3f_783_){
_start:
{
if (lean_obj_tag(v_saved_x3f_783_) == 0)
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_s_781_, v_fvarId_782_);
lean_dec(v_fvarId_782_);
return v___x_784_;
}
else
{
lean_object* v_val_785_; lean_object* v___y_787_; lean_object* v_i_788_; lean_object* v___y_794_; lean_object* v___y_804_; lean_object* v_i_805_; lean_object* v___x_820_; 
v_val_785_ = lean_ctor_get(v_saved_x3f_783_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v_saved_x3f_783_, 1);
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v_s_781_, v_fvarId_782_);
switch(lean_obj_tag(v___x_820_))
{
case 0:
{
lean_object* v_index_821_; lean_object* v_size_822_; lean_object* v___x_823_; 
v_index_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_index_821_);
lean_dec_ref_known(v___x_820_, 3);
v_size_822_ = lean_ctor_get(v_s_781_, 0);
lean_inc(v_size_822_);
v___x_823_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_781_, v_size_822_, v_index_821_, v_fvarId_782_, v_val_785_);
lean_dec(v_index_821_);
return v___x_823_;
}
case 1:
{
lean_object* v_index_824_; lean_object* v_size_825_; lean_object* v_keyArray_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_index_824_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_index_824_);
lean_dec_ref_known(v___x_820_, 1);
v_size_825_ = lean_ctor_get(v_s_781_, 0);
v_keyArray_826_ = lean_ctor_get(v_s_781_, 1);
v___x_827_ = lean_unsigned_to_nat(1u);
v___x_828_ = lean_nat_add(v_size_825_, v___x_827_);
v___x_829_ = lean_array_get_size(v_keyArray_826_);
v___x_830_ = lean_nat_dec_lt(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
lean_dec(v___x_828_);
lean_dec(v_index_824_);
goto v___jp_810_;
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_831_ = lean_unsigned_to_nat(4u);
v___x_832_ = lean_nat_mul(v___x_828_, v___x_831_);
v___x_833_ = lean_unsigned_to_nat(3u);
v___x_834_ = lean_nat_mul(v___x_829_, v___x_833_);
v___x_835_ = lean_nat_dec_le(v___x_832_, v___x_834_);
lean_dec(v___x_834_);
lean_dec(v___x_832_);
if (v___x_835_ == 0)
{
lean_dec(v___x_828_);
lean_dec(v_index_824_);
goto v___jp_810_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_781_, v___x_828_, v_index_824_, v_fvarId_782_, v_val_785_);
lean_dec(v_index_824_);
return v___x_836_;
}
}
}
default: 
{
lean_object* v_size_837_; lean_object* v_keyArray_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_size_837_ = lean_ctor_get(v_s_781_, 0);
v_keyArray_838_ = lean_ctor_get(v_s_781_, 1);
v___x_839_ = lean_unsigned_to_nat(1u);
v___x_840_ = lean_nat_add(v_size_837_, v___x_839_);
v___x_841_ = lean_array_get_size(v_keyArray_838_);
v___x_842_ = lean_nat_dec_lt(v___x_840_, v___x_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; 
lean_dec(v___x_840_);
v___x_843_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_781_);
lean_dec_ref(v_s_781_);
v___y_794_ = v___x_843_;
goto v___jp_793_;
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_844_ = lean_unsigned_to_nat(4u);
v___x_845_ = lean_nat_mul(v___x_840_, v___x_844_);
lean_dec(v___x_840_);
v___x_846_ = lean_unsigned_to_nat(3u);
v___x_847_ = lean_nat_mul(v___x_841_, v___x_846_);
v___x_848_ = lean_nat_dec_le(v___x_845_, v___x_847_);
lean_dec(v___x_847_);
lean_dec(v___x_845_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_781_);
lean_dec_ref(v_s_781_);
v___y_794_ = v___x_849_;
goto v___jp_793_;
}
else
{
v___y_794_ = v_s_781_;
goto v___jp_793_;
}
}
}
}
v___jp_786_:
{
lean_object* v_size_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_size_789_ = lean_ctor_get(v___y_787_, 0);
v___x_790_ = lean_unsigned_to_nat(1u);
v___x_791_ = lean_nat_add(v_size_789_, v___x_790_);
v___x_792_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_787_, v___x_791_, v_i_788_, v_fvarId_782_, v_val_785_);
lean_dec(v_i_788_);
return v___x_792_;
}
v___jp_793_:
{
lean_object* v___x_795_; 
v___x_795_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___y_794_, v_fvarId_782_);
switch(lean_obj_tag(v___x_795_))
{
case 0:
{
lean_object* v_index_796_; lean_object* v_size_797_; lean_object* v___x_798_; 
v_index_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_index_796_);
lean_dec_ref_known(v___x_795_, 3);
v_size_797_ = lean_ctor_get(v___y_794_, 0);
lean_inc(v_size_797_);
v___x_798_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_794_, v_size_797_, v_index_796_, v_fvarId_782_, v_val_785_);
lean_dec(v_index_796_);
return v___x_798_;
}
case 1:
{
lean_object* v_index_799_; 
v_index_799_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_index_799_);
lean_dec_ref_known(v___x_795_, 1);
v___y_787_ = v___y_794_;
v_i_788_ = v_index_799_;
goto v___jp_786_;
}
default: 
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_794_, v___x_800_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_index_802_; 
v_index_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_index_802_);
lean_dec_ref_known(v___x_801_, 1);
v___y_787_ = v___y_794_;
v_i_788_ = v_index_802_;
goto v___jp_786_;
}
else
{
lean_dec(v_val_785_);
lean_dec(v_fvarId_782_);
return v___y_794_;
}
}
}
}
v___jp_803_:
{
lean_object* v_size_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_size_806_ = lean_ctor_get(v___y_804_, 0);
v___x_807_ = lean_unsigned_to_nat(1u);
v___x_808_ = lean_nat_add(v_size_806_, v___x_807_);
v___x_809_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_804_, v___x_808_, v_i_805_, v_fvarId_782_, v_val_785_);
lean_dec(v_i_805_);
return v___x_809_;
}
v___jp_810_:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__2___redArg(v_s_781_);
lean_dec_ref(v_s_781_);
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add_spec__1___redArg(v___x_811_, v_fvarId_782_);
switch(lean_obj_tag(v___x_812_))
{
case 0:
{
lean_object* v_index_813_; lean_object* v_size_814_; lean_object* v___x_815_; 
v_index_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_index_813_);
lean_dec_ref_known(v___x_812_, 3);
v_size_814_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_size_814_);
v___x_815_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_811_, v_size_814_, v_index_813_, v_fvarId_782_, v_val_785_);
lean_dec(v_index_813_);
return v___x_815_;
}
case 1:
{
lean_object* v_index_816_; 
v_index_816_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_index_816_);
lean_dec_ref_known(v___x_812_, 1);
v___y_804_ = v___x_811_;
v_i_805_ = v_index_816_;
goto v___jp_803_;
}
default: 
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_811_, v___x_817_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_index_819_; 
v_index_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_index_819_);
lean_dec_ref_known(v___x_818_, 1);
v___y_804_ = v___x_811_;
v_i_805_ = v_index_819_;
goto v___jp_803_;
}
else
{
lean_dec(v_val_785_);
lean_dec(v_fvarId_782_);
return v___x_811_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(lean_object* v_00_u03b2_850_, lean_object* v_m_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___redArg(v_m_851_, v_a_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0___boxed(lean_object* v_00_u03b2_854_, lean_object* v_m_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_Compiler_LCNF_Simp_FunDeclInfoMap_restore_spec__0(v_00_u03b2_854_, v_m_855_, v_a_856_);
lean_dec(v_a_856_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(lean_object* v_arg_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
if (lean_obj_tag(v_arg_858_) == 1)
{
lean_object* v_fvarId_862_; uint8_t v___x_863_; lean_object* v___x_864_; 
v_fvarId_862_ = lean_ctor_get(v_arg_858_, 0);
lean_inc(v_fvarId_862_);
lean_dec_ref_known(v_arg_858_, 1);
v___x_863_ = 0;
v___x_864_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_863_, v_fvarId_862_, v_a_860_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_882_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_882_ == 0)
{
v___x_867_ = v___x_864_;
v_isShared_868_ = v_isSharedCheck_882_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_864_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_882_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
if (lean_obj_tag(v_a_865_) == 1)
{
lean_object* v_val_869_; lean_object* v___x_870_; lean_object* v_fvarId_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
v_val_869_ = lean_ctor_get(v_a_865_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v_a_865_, 1);
v___x_870_ = lean_st_ref_take(v_a_859_);
v_fvarId_871_ = lean_ctor_get(v_val_869_, 0);
lean_inc(v_fvarId_871_);
lean_dec(v_val_869_);
v___x_872_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addHo(v___x_870_, v_fvarId_871_);
v___x_873_ = lean_st_ref_put(v_a_859_, v___x_872_);
v___x_874_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_874_);
v___x_876_ = v___x_867_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_880_; 
lean_dec(v_a_865_);
v___x_878_ = lean_box(0);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 0, v___x_878_);
v___x_880_ = v___x_867_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_864_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_864_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec(v_arg_858_);
v___x_891_ = lean_box(0);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg___boxed(lean_object* v_arg_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(lean_object* v_arg_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v_arg_898_, v_a_899_, v_a_901_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___boxed(lean_object* v_arg_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc(v_arg_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(lean_object* v_as_914_, size_t v_i_915_, size_t v_stop_916_, lean_object* v_b_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = lean_usize_dec_eq(v_i_915_, v_stop_916_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_array_uget_borrowed(v_as_914_, v_i_915_);
lean_inc(v___x_922_);
v___x_923_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addArgOcc___redArg(v___x_922_, v___y_918_, v___y_919_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; size_t v___x_925_; size_t v___x_926_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref_known(v___x_923_, 1);
v___x_925_ = ((size_t)1ULL);
v___x_926_ = lean_usize_add(v_i_915_, v___x_925_);
v_i_915_ = v___x_926_;
v_b_917_ = v_a_924_;
goto _start;
}
else
{
return v___x_923_;
}
}
else
{
lean_object* v___x_928_; 
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v_b_917_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg___boxed(lean_object* v_as_929_, lean_object* v_i_930_, lean_object* v_stop_931_, lean_object* v_b_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
size_t v_i_boxed_936_; size_t v_stop_boxed_937_; lean_object* v_res_938_; 
v_i_boxed_936_ = lean_unbox_usize(v_i_930_);
lean_dec(v_i_930_);
v_stop_boxed_937_ = lean_unbox_usize(v_stop_931_);
lean_dec(v_stop_931_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_929_, v_i_boxed_936_, v_stop_boxed_937_, v_b_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v_as_929_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(lean_object* v_e_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
switch(lean_obj_tag(v_e_939_))
{
case 0:
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
v_isSharedCheck_953_ = !lean_is_exclusive(v_e_939_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_e_939_, 0);
lean_dec(v_unused_954_);
v___x_947_ = v_e_939_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_dec(v_e_939_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_951_; 
v___x_949_ = lean_box(0);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_951_ = v___x_947_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
case 3:
{
lean_object* v_args_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_args_955_ = lean_ctor_get(v_e_939_, 2);
lean_inc_ref(v_args_955_);
lean_dec_ref_known(v_e_939_, 3);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_array_get_size(v_args_955_);
v___x_958_ = lean_box(0);
v___x_959_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v_args_955_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_958_);
return v___x_960_;
}
else
{
uint8_t v___x_961_; 
v___x_961_ = lean_nat_dec_le(v___x_957_, v___x_957_);
if (v___x_961_ == 0)
{
if (v___x_959_ == 0)
{
lean_object* v___x_962_; 
lean_dec_ref(v_args_955_);
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v___x_958_);
return v___x_962_;
}
else
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v___x_963_ = ((size_t)0ULL);
v___x_964_ = lean_usize_of_nat(v___x_957_);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_955_, v___x_963_, v___x_964_, v___x_958_, v_a_940_, v_a_942_);
lean_dec_ref(v_args_955_);
return v___x_965_;
}
}
else
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((size_t)0ULL);
v___x_967_ = lean_usize_of_nat(v___x_957_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_955_, v___x_966_, v___x_967_, v___x_958_, v_a_940_, v_a_942_);
lean_dec_ref(v_args_955_);
return v___x_968_;
}
}
}
case 4:
{
lean_object* v_fvarId_969_; lean_object* v_args_970_; uint8_t v___x_971_; lean_object* v___x_972_; 
v_fvarId_969_ = lean_ctor_get(v_e_939_, 0);
lean_inc(v_fvarId_969_);
v_args_970_ = lean_ctor_get(v_e_939_, 1);
lean_inc_ref(v_args_970_);
lean_dec_ref_known(v_e_939_, 2);
v___x_971_ = 0;
v___x_972_ = l_Lean_Compiler_LCNF_Simp_findFunDecl_x27_x3f___redArg(v___x_971_, v_fvarId_969_, v_a_942_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1003_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_1003_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1003_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
if (lean_obj_tag(v_a_973_) == 1)
{
lean_object* v_val_977_; lean_object* v___x_978_; lean_object* v_fvarId_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_val_977_ = lean_ctor_get(v_a_973_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_a_973_, 1);
v___x_978_ = lean_st_ref_take(v_a_940_);
v_fvarId_979_ = lean_ctor_get(v_val_977_, 0);
lean_inc(v_fvarId_979_);
lean_dec(v_val_977_);
v___x_980_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_978_, v_fvarId_979_);
v___x_981_ = lean_st_ref_put(v_a_940_, v___x_980_);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = lean_array_get_size(v_args_970_);
v___x_984_ = lean_box(0);
v___x_985_ = lean_nat_dec_lt(v___x_982_, v___x_983_);
if (v___x_985_ == 0)
{
lean_object* v___x_987_; 
lean_dec_ref(v_args_970_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_984_);
v___x_987_ = v___x_975_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_984_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
uint8_t v___x_989_; 
v___x_989_ = lean_nat_dec_le(v___x_983_, v___x_983_);
if (v___x_989_ == 0)
{
if (v___x_985_ == 0)
{
lean_object* v___x_991_; 
lean_dec_ref(v_args_970_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_984_);
v___x_991_ = v___x_975_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_984_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
else
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
lean_del_object(v___x_975_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_983_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_970_, v___x_993_, v___x_994_, v___x_984_, v_a_940_, v_a_942_);
lean_dec_ref(v_args_970_);
return v___x_995_;
}
}
else
{
size_t v___x_996_; size_t v___x_997_; lean_object* v___x_998_; 
lean_del_object(v___x_975_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = lean_usize_of_nat(v___x_983_);
v___x_998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_970_, v___x_996_, v___x_997_, v___x_984_, v_a_940_, v_a_942_);
lean_dec_ref(v_args_970_);
return v___x_998_;
}
}
}
else
{
lean_object* v___x_999_; lean_object* v___x_1001_; 
lean_dec(v_a_973_);
lean_dec_ref(v_args_970_);
v___x_999_ = lean_box(0);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_999_);
v___x_1001_ = v___x_975_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_999_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_args_970_);
v_a_1004_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_972_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_972_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
default: 
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_e_939_);
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs___boxed(lean_object* v_e_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_e_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(lean_object* v_as_1022_, size_t v_i_1023_, size_t v_stop_1024_, lean_object* v_b_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_as_1022_, v_i_1023_, v_stop_1024_, v_b_1025_, v___y_1026_, v___y_1028_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___boxed(lean_object* v_as_1033_, lean_object* v_i_1034_, lean_object* v_stop_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
size_t v_i_boxed_1043_; size_t v_stop_boxed_1044_; lean_object* v_res_1045_; 
v_i_boxed_1043_ = lean_unbox_usize(v_i_1034_);
lean_dec(v_i_1034_);
v_stop_boxed_1044_ = lean_unbox_usize(v_stop_1035_);
lean_dec(v_stop_1035_);
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0(v_as_1033_, v_i_boxed_1043_, v_stop_boxed_1044_, v_b_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v_as_1033_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(uint8_t v_mustInline_1046_, lean_object* v_code_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_){
_start:
{
switch(lean_obj_tag(v_code_1047_))
{
case 0:
{
lean_object* v_decl_1054_; lean_object* v_k_1055_; lean_object* v_value_1056_; lean_object* v___x_1057_; 
v_decl_1054_ = lean_ctor_get(v_code_1047_, 0);
lean_inc_ref(v_decl_1054_);
v_k_1055_ = lean_ctor_get(v_code_1047_, 1);
lean_inc_ref(v_k_1055_);
lean_dec_ref_known(v_code_1047_, 2);
v_value_1056_ = lean_ctor_get(v_decl_1054_, 3);
lean_inc(v_value_1056_);
lean_dec_ref(v_decl_1054_);
v___x_1057_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs(v_value_1056_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_dec_ref_known(v___x_1057_, 1);
v_code_1047_ = v_k_1055_;
goto _start;
}
else
{
lean_dec_ref(v_k_1055_);
return v___x_1057_;
}
}
case 1:
{
lean_object* v_decl_1059_; lean_object* v_k_1060_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; 
v_decl_1059_ = lean_ctor_get(v_code_1047_, 0);
lean_inc_ref(v_decl_1059_);
v_k_1060_ = lean_ctor_get(v_code_1047_, 1);
lean_inc_ref(v_k_1060_);
lean_dec_ref_known(v_code_1047_, 2);
if (v_mustInline_1046_ == 0)
{
v___y_1062_ = v_a_1048_;
v___y_1063_ = v_a_1049_;
v___y_1064_ = v_a_1050_;
v___y_1065_ = v_a_1051_;
v___y_1066_ = v_a_1052_;
goto v___jp_1061_;
}
else
{
lean_object* v___x_1070_; lean_object* v_fvarId_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1070_ = lean_st_ref_take(v_a_1048_);
v_fvarId_1071_ = lean_ctor_get(v_decl_1059_, 0);
lean_inc(v_fvarId_1071_);
v___x_1072_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_addMustInline(v___x_1070_, v_fvarId_1071_);
v___x_1073_ = lean_st_ref_put(v_a_1048_, v___x_1072_);
v___y_1062_ = v_a_1048_;
v___y_1063_ = v_a_1049_;
v___y_1064_ = v_a_1050_;
v___y_1065_ = v_a_1051_;
v___y_1066_ = v_a_1052_;
goto v___jp_1061_;
}
v___jp_1061_:
{
lean_object* v_value_1067_; lean_object* v___x_1068_; 
v_value_1067_ = lean_ctor_get(v_decl_1059_, 4);
lean_inc_ref(v_value_1067_);
lean_dec_ref(v_decl_1059_);
v___x_1068_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1046_, v_value_1067_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_dec_ref_known(v___x_1068_, 1);
v_code_1047_ = v_k_1060_;
v_a_1048_ = v___y_1062_;
v_a_1049_ = v___y_1063_;
v_a_1050_ = v___y_1064_;
v_a_1051_ = v___y_1065_;
v_a_1052_ = v___y_1066_;
goto _start;
}
else
{
lean_dec_ref(v_k_1060_);
return v___x_1068_;
}
}
}
case 2:
{
lean_object* v_decl_1074_; lean_object* v_k_1075_; lean_object* v_value_1076_; lean_object* v___x_1077_; 
v_decl_1074_ = lean_ctor_get(v_code_1047_, 0);
lean_inc_ref(v_decl_1074_);
v_k_1075_ = lean_ctor_get(v_code_1047_, 1);
lean_inc_ref(v_k_1075_);
lean_dec_ref_known(v_code_1047_, 2);
v_value_1076_ = lean_ctor_get(v_decl_1074_, 4);
lean_inc_ref(v_value_1076_);
lean_dec_ref(v_decl_1074_);
v___x_1077_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1046_, v_value_1076_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_dec_ref_known(v___x_1077_, 1);
v_code_1047_ = v_k_1075_;
goto _start;
}
else
{
lean_dec_ref(v_k_1075_);
return v___x_1077_;
}
}
case 3:
{
lean_object* v_fvarId_1079_; lean_object* v_args_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; 
v_fvarId_1079_ = lean_ctor_get(v_code_1047_, 0);
lean_inc(v_fvarId_1079_);
v_args_1080_ = lean_ctor_get(v_code_1047_, 1);
lean_inc_ref(v_args_1080_);
lean_dec_ref_known(v_code_1047_, 2);
v___x_1081_ = 0;
v___x_1082_ = l_Lean_Compiler_LCNF_getFunDecl(v___x_1081_, v_fvarId_1079_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1108_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1108_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1108_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v_fvarId_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1087_ = lean_st_ref_take(v_a_1048_);
v_fvarId_1088_ = lean_ctor_get(v_a_1083_, 0);
lean_inc(v_fvarId_1088_);
lean_dec(v_a_1083_);
v___x_1089_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_add(v___x_1087_, v_fvarId_1088_);
v___x_1090_ = lean_st_ref_put(v_a_1048_, v___x_1089_);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_array_get_size(v_args_1080_);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_nat_dec_lt(v___x_1091_, v___x_1092_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1096_; 
lean_dec_ref(v_args_1080_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1093_);
v___x_1096_ = v___x_1085_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1093_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
else
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_le(v___x_1092_, v___x_1092_);
if (v___x_1098_ == 0)
{
if (v___x_1094_ == 0)
{
lean_object* v___x_1100_; 
lean_dec_ref(v_args_1080_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1093_);
v___x_1100_ = v___x_1085_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1093_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
size_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
lean_del_object(v___x_1085_);
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = lean_usize_of_nat(v___x_1092_);
v___x_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1080_, v___x_1102_, v___x_1103_, v___x_1093_, v_a_1048_, v_a_1050_);
lean_dec_ref(v_args_1080_);
return v___x_1104_;
}
}
else
{
size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; 
lean_del_object(v___x_1085_);
v___x_1105_ = ((size_t)0ULL);
v___x_1106_ = lean_usize_of_nat(v___x_1092_);
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_addLetValueOccs_spec__0___redArg(v_args_1080_, v___x_1105_, v___x_1106_, v___x_1093_, v_a_1048_, v_a_1050_);
lean_dec_ref(v_args_1080_);
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec_ref(v_args_1080_);
v_a_1109_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1082_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1082_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
case 4:
{
lean_object* v_cases_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1139_; 
v_cases_1117_ = lean_ctor_get(v_code_1047_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_code_1047_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1119_ = v_code_1047_;
v_isShared_1120_ = v_isSharedCheck_1139_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_cases_1117_);
lean_dec(v_code_1047_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1139_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v_alts_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; 
v_alts_1121_ = lean_ctor_get(v_cases_1117_, 3);
lean_inc_ref(v_alts_1121_);
lean_dec_ref(v_cases_1117_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_array_get_size(v_alts_1121_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_nat_dec_lt(v___x_1122_, v___x_1123_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1127_; 
lean_dec_ref(v_alts_1121_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1124_);
v___x_1127_ = v___x_1119_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1124_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_nat_dec_le(v___x_1123_, v___x_1123_);
if (v___x_1129_ == 0)
{
if (v___x_1125_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_alts_1121_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set_tag(v___x_1119_, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1124_);
v___x_1131_ = v___x_1119_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1124_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_1119_);
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = lean_usize_of_nat(v___x_1123_);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_1046_, v_alts_1121_, v___x_1133_, v___x_1134_, v___x_1124_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec_ref(v_alts_1121_);
return v___x_1135_;
}
}
else
{
size_t v___x_1136_; size_t v___x_1137_; lean_object* v___x_1138_; 
lean_del_object(v___x_1119_);
v___x_1136_ = ((size_t)0ULL);
v___x_1137_ = lean_usize_of_nat(v___x_1123_);
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_1046_, v_alts_1121_, v___x_1136_, v___x_1137_, v___x_1124_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec_ref(v_alts_1121_);
return v___x_1138_;
}
}
}
}
default: 
{
lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1147_; 
v_isSharedCheck_1147_ = !lean_is_exclusive(v_code_1047_);
if (v_isSharedCheck_1147_ == 0)
{
lean_object* v_unused_1148_; 
v_unused_1148_ = lean_ctor_get(v_code_1047_, 0);
lean_dec(v_unused_1148_);
v___x_1141_ = v_code_1047_;
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
else
{
lean_dec(v_code_1047_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1147_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(0);
if (v_isShared_1142_ == 0)
{
lean_ctor_set_tag(v___x_1141_, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1143_);
v___x_1145_ = v___x_1141_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(uint8_t v_mustInline_1149_, lean_object* v_as_1150_, size_t v_i_1151_, size_t v_stop_1152_, lean_object* v_b_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v___y_1161_; uint8_t v___x_1167_; 
v___x_1167_ = lean_usize_dec_eq(v_i_1151_, v_stop_1152_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_array_uget_borrowed(v_as_1150_, v_i_1151_);
switch(lean_obj_tag(v___x_1168_))
{
case 0:
{
lean_object* v_code_1169_; 
v_code_1169_ = lean_ctor_get(v___x_1168_, 2);
lean_inc_ref(v_code_1169_);
v___y_1161_ = v_code_1169_;
goto v___jp_1160_;
}
case 1:
{
lean_object* v_code_1170_; 
v_code_1170_ = lean_ctor_get(v___x_1168_, 1);
lean_inc_ref(v_code_1170_);
v___y_1161_ = v_code_1170_;
goto v___jp_1160_;
}
default: 
{
lean_object* v_code_1171_; 
v_code_1171_ = lean_ctor_get(v___x_1168_, 0);
lean_inc_ref(v_code_1171_);
v___y_1161_ = v_code_1171_;
goto v___jp_1160_;
}
}
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_b_1153_);
return v___x_1172_;
}
v___jp_1160_:
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1149_, v___y_1161_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_, v___y_1158_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; size_t v___x_1164_; size_t v___x_1165_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = ((size_t)1ULL);
v___x_1165_ = lean_usize_add(v_i_1151_, v___x_1164_);
v_i_1151_ = v___x_1165_;
v_b_1153_ = v_a_1163_;
goto _start;
}
else
{
return v___x_1162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0___boxed(lean_object* v_mustInline_1173_, lean_object* v_as_1174_, lean_object* v_i_1175_, lean_object* v_stop_1176_, lean_object* v_b_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v_mustInline_boxed_1184_; size_t v_i_boxed_1185_; size_t v_stop_boxed_1186_; lean_object* v_res_1187_; 
v_mustInline_boxed_1184_ = lean_unbox(v_mustInline_1173_);
v_i_boxed_1185_ = lean_unbox_usize(v_i_1175_);
lean_dec(v_i_1175_);
v_stop_boxed_1186_ = lean_unbox_usize(v_stop_1176_);
lean_dec(v_stop_1176_);
v_res_1187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go_spec__0(v_mustInline_boxed_1184_, v_as_1174_, v_i_boxed_1185_, v_stop_boxed_1186_, v_b_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v_as_1174_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go___boxed(lean_object* v_mustInline_1188_, lean_object* v_code_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_){
_start:
{
uint8_t v_mustInline_boxed_1196_; lean_object* v_res_1197_; 
v_mustInline_boxed_1196_ = lean_unbox(v_mustInline_1188_);
v_res_1197_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_boxed_1196_, v_code_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
lean_dec(v_a_1194_);
lean_dec_ref(v_a_1193_);
lean_dec(v_a_1192_);
lean_dec_ref(v_a_1191_);
lean_dec(v_a_1190_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(lean_object* v_s_1198_, lean_object* v_code_1199_, uint8_t v_mustInline_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_st_mk_ref(v_s_1198_);
v___x_1207_ = l___private_Lean_Compiler_LCNF_Simp_FunDeclInfo_0__Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update_go(v_mustInline_1200_, v_code_1199_, v___x_1206_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_);
if (lean_obj_tag(v___x_1207_) == 0)
{
lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1207_, 0);
lean_dec(v_unused_1216_);
v___x_1209_ = v___x_1207_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_dec(v___x_1207_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_st_ref_get(v___x_1206_);
lean_dec(v___x_1206_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1211_);
v___x_1213_ = v___x_1209_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v___x_1206_);
v_a_1217_ = lean_ctor_get(v___x_1207_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1207_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1207_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update___boxed(lean_object* v_s_1225_, lean_object* v_code_1226_, lean_object* v_mustInline_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
uint8_t v_mustInline_boxed_1233_; lean_object* v_res_1234_; 
v_mustInline_boxed_1233_ = lean_unbox(v_mustInline_1227_);
v_res_1234_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_update(v_s_1225_, v_code_1226_, v_mustInline_boxed_1233_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
return v_res_1234_;
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

// Lean compiler output
// Module: Lean.Syntax
// Imports: public import Init.Data.Slice public import Init.Data.Hashable public import Lean.Data.Format public import Init.Data.Option.Coe public import Init.Data.String.Hashable import Init.Data.Range.Polymorphic.Iterators import Init.Data.ToString.Macro import Init.Omega import Init.Syntax
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_instBEqPreresolved_beq(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_SourceInfo_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_substring_tostring(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_Substring_Raw_beq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_SourceInfo_getTailPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTrailingTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailInfo_x3f(lean_object*);
lean_object* l_Lean_Syntax_setTailInfo(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_dropLastComponents(lean_object*, lean_object*);
lean_object* l_Lean_Name_revIter(lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
lean_object* l_Lean_Syntax_splitNameLit(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Syntax_instInhabitedRange_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instInhabitedRange_default___closed__0 = (const lean_object*)&l_Lean_Syntax_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instInhabitedRange_default = (const lean_object*)&l_Lean_Syntax_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instInhabitedRange = (const lean_object*)&l_Lean_Syntax_instInhabitedRange_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Syntax_instReprRange_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__7;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "{ byteIdx := "};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__11_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__12 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__12_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__13_value;
static const lean_string_object l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__14 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__14_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__15 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__15_value;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__16;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__17;
static lean_once_cell_t l_Lean_Syntax_instReprRange_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__18;
static const lean_ctor_object l_Lean_Syntax_instReprRange_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instReprRange_repr___redArg___closed__19 = (const lean_object*)&l_Lean_Syntax_instReprRange_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instReprRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instReprRange_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instReprRange___closed__0 = (const lean_object*)&l_Lean_Syntax_instReprRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instReprRange = (const lean_object*)&l_Lean_Syntax_instReprRange___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_instBEqRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instBEqRange_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instBEqRange___closed__0 = (const lean_object*)&l_Lean_Syntax_instBEqRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instBEqRange = (const lean_object*)&l_Lean_Syntax_instBEqRange___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_instHashableRange___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instHashableRange_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instHashableRange___closed__0 = (const lean_object*)&l_Lean_Syntax_instHashableRange___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instHashableRange = (const lean_object*)&l_Lean_Syntax_instHashableRange___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqSourceInfo__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqSourceInfo__lean_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqSourceInfo__lean___closed__0 = (const lean_object*)&l_Lean_instBEqSourceInfo__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqSourceInfo__lean = (const lean_object*)&l_Lean_instBEqSourceInfo__lean___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing___redArg();
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___redArg();
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___redArg();
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isLitKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_isLitKind___closed__0 = (const lean_object*)&l_Lean_isLitKind___closed__0_value;
static const lean_ctor_object l_Lean_isLitKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_isLitKind___closed__1 = (const lean_object*)&l_Lean_isLitKind___closed__1_value;
static const lean_string_object l_Lean_isLitKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_isLitKind___closed__2 = (const lean_object*)&l_Lean_isLitKind___closed__2_value;
static const lean_ctor_object l_Lean_isLitKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_isLitKind___closed__3 = (const lean_object*)&l_Lean_isLitKind___closed__3_value;
static const lean_string_object l_Lean_isLitKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "char"};
static const lean_object* l_Lean_isLitKind___closed__4 = (const lean_object*)&l_Lean_isLitKind___closed__4_value;
static const lean_ctor_object l_Lean_isLitKind___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__4_value),LEAN_SCALAR_PTR_LITERAL(43, 243, 213, 66, 253, 140, 152, 232)}};
static const lean_object* l_Lean_isLitKind___closed__5 = (const lean_object*)&l_Lean_isLitKind___closed__5_value;
static const lean_string_object l_Lean_isLitKind___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lean_isLitKind___closed__6 = (const lean_object*)&l_Lean_isLitKind___closed__6_value;
static const lean_ctor_object l_Lean_isLitKind___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__6_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lean_isLitKind___closed__7 = (const lean_object*)&l_Lean_isLitKind___closed__7_value;
static const lean_string_object l_Lean_isLitKind___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "scientific"};
static const lean_object* l_Lean_isLitKind___closed__8 = (const lean_object*)&l_Lean_isLitKind___closed__8_value;
static const lean_ctor_object l_Lean_isLitKind___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isLitKind___closed__8_value),LEAN_SCALAR_PTR_LITERAL(219, 104, 254, 176, 65, 57, 101, 179)}};
static const lean_object* l_Lean_isLitKind___closed__9 = (const lean_object*)&l_Lean_isLitKind___closed__9_value;
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "reuse"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value_aux_0),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 30, 230, 20, 64, 162, 204, 1)}};
static const lean_ctor_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value_aux_1),((lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__2_value),LEAN_SCALAR_PTR_LITERAL(32, 17, 142, 189, 192, 166, 31, 124)}};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "reuse stopped:\n"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4_value;
static const lean_string_object l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " !=\n"};
static const lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5 = (const lean_object*)&l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_getAtomVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Syntax_getAtomVal___closed__0 = (const lean_object*)&l_Lean_Syntax_getAtomVal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_asNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_asNode___closed__0 = (const lean_object*)&l_Lean_Syntax_asNode___closed__0_value;
static const lean_string_object l_Lean_Syntax_asNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Syntax_asNode___closed__1 = (const lean_object*)&l_Lean_Syntax_asNode___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_asNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_asNode___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Syntax_asNode___closed__2 = (const lean_object*)&l_Lean_Syntax_asNode___closed__2_value;
static const lean_ctor_object l_Lean_Syntax_asNode___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Syntax_asNode___closed__2_value),((lean_object*)&l_Lean_Syntax_asNode___closed__0_value)}};
static const lean_object* l_Lean_Syntax_asNode___closed__3 = (const lean_object*)&l_Lean_Syntax_asNode___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__0 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__0_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__1 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__1_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__2 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__2_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__3 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__3_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__4 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__4_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__5 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__5_value;
static const lean_closure_object l_Lean_Syntax_rewriteBottomUp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__6 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_rewriteBottomUp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__0_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__1_value)}};
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__7 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__7_value;
static const lean_ctor_object l_Lean_Syntax_rewriteBottomUp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__7_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__2_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__3_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__4_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__5_value)}};
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__8 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_rewriteBottomUp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__8_value),((lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__6_value)}};
static const lean_object* l_Lean_Syntax_rewriteBottomUp___closed__9 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUp___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__0(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__2 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__2_value;
static const lean_string_object l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__1 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__1_value;
static const lean_string_object l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__0 = (const lean_object*)&l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_eraseQuoteMacroScopes(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Syntax_getAtomVal___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0_value;
static const lean_string_object l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Syntax_identComponents_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_identComponents_x3f___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__0_value;
static const lean_array_object l_Lean_Syntax_identComponents_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__1 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__1_value;
static const lean_array_object l_Lean_Syntax_identComponents_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__2 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__2_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.Syntax"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__3 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__3_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Syntax.identComponents\?"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__4 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__4_value;
static const lean_string_object l_Lean_Syntax_identComponents_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Syntax_identComponents_x3f___closed__5 = (const lean_object*)&l_Lean_Syntax_identComponents_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Syntax_identComponents_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_identComponents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Syntax.identComponents"};
static const lean_object* l_Lean_Syntax_identComponents___closed__0 = (const lean_object*)&l_Lean_Syntax_identComponents___closed__0_value;
static lean_once_cell_t l_Lean_Syntax_identComponents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_identComponents___closed__1;
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "choice"};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 66, 148, 42, 181, 100, 85, 166)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0 = (const lean_object*)&l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__0_value)}};
static const lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Syntax_Traverser_fromSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_Traverser_fromSyntax___closed__0 = (const lean_object*)&l_Lean_Syntax_Traverser_fromSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object*);
static const lean_string_object l_Lean_Syntax_isQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Syntax_isQuot___closed__0 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__0_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "dynamicQuot"};
static const lean_object* l_Lean_Syntax_isQuot___closed__1 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__1_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Syntax_isQuot___closed__2 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__2_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Syntax_isQuot___closed__3 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__3_value;
static const lean_string_object l_Lean_Syntax_isQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Syntax_isQuot___closed__4 = (const lean_object*)&l_Lean_Syntax_isQuot___closed__4_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object*);
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value_aux_0),((lean_object*)&l_Lean_Syntax_isQuot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value_aux_1),((lean_object*)&l_Lean_Syntax_isQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_getQuotContent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value_aux_2),((lean_object*)&l_Lean_Syntax_isQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 123, 139, 164, 173, 191, 116, 242)}};
static const lean_object* l_Lean_Syntax_getQuotContent___closed__0 = (const lean_object*)&l_Lean_Syntax_getQuotContent___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
static const lean_string_object l_Lean_Syntax_isAntiquot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "antiquot"};
static const lean_object* l_Lean_Syntax_isAntiquot___closed__0 = (const lean_object*)&l_Lean_Syntax_isAntiquot___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object*);
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__0 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__0_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__1;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isAntiquot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 141, 12, 45, 178, 67, 53, 106)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__2 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__2_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__3;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "pseudo"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__4 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__4_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__4_value),LEAN_SCALAR_PTR_LITERAL(246, 255, 48, 87, 29, 98, 48, 237)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__5 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__5_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "antiquotName"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__6 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__6_value),LEAN_SCALAR_PTR_LITERAL(67, 48, 35, 197, 163, 216, 250, 79)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__7 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__7_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__8 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__8_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__10;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__11 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__11_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_0),((lean_object*)&l_Lean_Syntax_isQuot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_1),((lean_object*)&l_Lean_Syntax_isQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value_aux_2),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__11_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__12 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__12_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "antiquotNestedExpr"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__13 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__13_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotNode___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__13_value),LEAN_SCALAR_PTR_LITERAL(4, 217, 111, 200, 191, 162, 168, 125)}};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__14 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__14_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__15 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__15_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__16;
static const lean_string_object l_Lean_Syntax_mkAntiquotNode___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Syntax_mkAntiquotNode___closed__17 = (const lean_object*)&l_Lean_Syntax_mkAntiquotNode___closed__17_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__18;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotNode___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotNode___closed__19;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object*);
static const lean_string_object l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "antiquot_scope"};
static const lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object*);
static const lean_string_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "antiquot_splice"};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__0 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 54, 194, 194, 68, 126, 190, 193)}};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__1 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__1_value;
static const lean_string_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__2 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__2_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__3;
static const lean_string_object l_Lean_Syntax_mkAntiquotSpliceNode___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__4 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSpliceNode___closed__4_value;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__5;
static lean_once_cell_t l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_mkAntiquotSpliceNode___closed__6;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "antiquot_suffix_splice"};
static const lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0 = (const lean_object*)&l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object*);
static const lean_ctor_object l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 22, 214, 220, 194, 127, 23, 217)}};
static const lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0 = (const lean_object*)&l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_isTokenAntiquot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "token_antiquot"};
static const lean_object* l_Lean_Syntax_isTokenAntiquot___closed__0 = (const lean_object*)&l_Lean_Syntax_isTokenAntiquot___closed__0_value;
static const lean_ctor_object l_Lean_Syntax_isTokenAntiquot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_isTokenAntiquot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(33, 159, 231, 44, 235, 156, 55, 135)}};
static const lean_object* l_Lean_Syntax_isTokenAntiquot___closed__1 = (const lean_object*)&l_Lean_Syntax_isTokenAntiquot___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0 = (const lean_object*)&l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object*);
static const lean_array_object l_Lean_Syntax_Stack_matches___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Syntax_Stack_matches___closed__0 = (const lean_object*)&l_Lean_Syntax_Stack_matches___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Syntax_instReprRange_repr_spec__0(lean_object* v_a_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_nat_to_int(v_a_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_20_ = lean_unsigned_to_nat(9u);
v___x_21_ = lean_nat_to_int(v___x_20_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_unsigned_to_nat(8u);
v___x_35_ = lean_nat_to_int(v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__0));
v___x_37_ = lean_string_length(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_38_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__17, &l_Lean_Syntax_instReprRange_repr___redArg___closed__17_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__17);
v___x_39_ = lean_nat_to_int(v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___redArg(lean_object* v_x_42_){
_start:
{
lean_object* v_start_43_; lean_object* v_stop_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_84_; 
v_start_43_ = lean_ctor_get(v_x_42_, 0);
v_stop_44_ = lean_ctor_get(v_x_42_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_84_ == 0)
{
v___x_46_ = v_x_42_;
v_isShared_47_ = v_isSharedCheck_84_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_stop_44_);
lean_inc(v_start_43_);
lean_dec(v_x_42_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_84_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_48_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__5));
v___x_49_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__6));
v___x_50_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__7, &l_Lean_Syntax_instReprRange_repr___redArg___closed__7_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__7);
v___x_51_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__9));
v___x_52_ = l_Nat_reprFast(v_start_43_);
v___x_53_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
if (v_isShared_47_ == 0)
{
lean_ctor_set_tag(v___x_46_, 5);
lean_ctor_set(v___x_46_, 1, v___x_53_);
lean_ctor_set(v___x_46_, 0, v___x_51_);
v___x_55_ = v___x_46_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_51_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_83_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_56_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__11));
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set(v___x_57_, 1, v___x_56_);
v___x_58_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_50_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
v___x_59_ = 0;
v___x_60_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_60_, 0, v___x_58_);
lean_ctor_set_uint8(v___x_60_, sizeof(void*)*1, v___x_59_);
v___x_61_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_49_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
v___x_62_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__13));
v___x_63_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_63_, 0, v___x_61_);
lean_ctor_set(v___x_63_, 1, v___x_62_);
v___x_64_ = lean_box(1);
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_63_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__15));
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v___x_48_);
v___x_69_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__16, &l_Lean_Syntax_instReprRange_repr___redArg___closed__16_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__16);
v___x_70_ = l_Nat_reprFast(v_stop_44_);
v___x_71_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_51_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
lean_ctor_set(v___x_73_, 1, v___x_56_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_69_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_75_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_75_, sizeof(void*)*1, v___x_59_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_68_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_obj_once(&l_Lean_Syntax_instReprRange_repr___redArg___closed__18, &l_Lean_Syntax_instReprRange_repr___redArg___closed__18_once, _init_l_Lean_Syntax_instReprRange_repr___redArg___closed__18);
v___x_78_ = ((lean_object*)(l_Lean_Syntax_instReprRange_repr___redArg___closed__19));
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_76_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_56_);
v___x_81_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_77_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
v___x_82_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*1, v___x_59_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr(lean_object* v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_Syntax_instReprRange_repr___redArg(v_x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instReprRange_repr___boxed(lean_object* v_x_88_, lean_object* v_prec_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Syntax_instReprRange_repr(v_x_88_, v_prec_89_);
lean_dec(v_prec_89_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_instBEqRange_beq(lean_object* v_x_93_, lean_object* v_x_94_){
_start:
{
lean_object* v_start_95_; lean_object* v_stop_96_; lean_object* v_start_97_; lean_object* v_stop_98_; uint8_t v_decide_99_; 
v_start_95_ = lean_ctor_get(v_x_93_, 0);
v_stop_96_ = lean_ctor_get(v_x_93_, 1);
v_start_97_ = lean_ctor_get(v_x_94_, 0);
v_stop_98_ = lean_ctor_get(v_x_94_, 1);
v_decide_99_ = lean_nat_dec_eq(v_start_95_, v_start_97_);
if (v_decide_99_ == 0)
{
return v_decide_99_;
}
else
{
uint8_t v_decide_100_; 
v_decide_100_ = lean_nat_dec_eq(v_stop_96_, v_stop_98_);
return v_decide_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instBEqRange_beq___boxed(lean_object* v_x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_Syntax_instBEqRange_beq(v_x_101_, v_x_102_);
lean_dec_ref(v_x_102_);
lean_dec_ref(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint64_t l_Lean_Syntax_instHashableRange_hash(lean_object* v_x_107_){
_start:
{
lean_object* v_start_108_; lean_object* v_stop_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v___x_113_; uint64_t v___x_114_; 
v_start_108_ = lean_ctor_get(v_x_107_, 0);
v_stop_109_ = lean_ctor_get(v_x_107_, 1);
v___x_110_ = 0ULL;
v___x_111_ = l_String_instHashableRaw_hash(v_start_108_);
v___x_112_ = lean_uint64_mix_hash(v___x_110_, v___x_111_);
v___x_113_ = l_String_instHashableRaw_hash(v_stop_109_);
v___x_114_ = lean_uint64_mix_hash(v___x_112_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instHashableRange_hash___boxed(lean_object* v_x_115_){
_start:
{
uint64_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_Syntax_instHashableRange_hash(v_x_115_);
lean_dec_ref(v_x_115_);
v_r_117_ = lean_box_uint64(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_contains(lean_object* v_r_120_, lean_object* v_pos_121_, uint8_t v_includeStop_122_){
_start:
{
lean_object* v_start_123_; lean_object* v_stop_124_; uint8_t v___x_125_; 
v_start_123_ = lean_ctor_get(v_r_120_, 0);
v_stop_124_ = lean_ctor_get(v_r_120_, 1);
v___x_125_ = lean_nat_dec_le(v_start_123_, v_pos_121_);
if (v___x_125_ == 0)
{
return v___x_125_;
}
else
{
if (v_includeStop_122_ == 0)
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v___x_127_ = lean_nat_add(v_pos_121_, v___x_126_);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_stop_124_);
lean_dec(v___x_127_);
return v___x_128_;
}
else
{
uint8_t v___x_129_; 
v___x_129_ = lean_nat_dec_le(v_pos_121_, v_stop_124_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_contains___boxed(lean_object* v_r_130_, lean_object* v_pos_131_, lean_object* v_includeStop_132_){
_start:
{
uint8_t v_includeStop_boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_includeStop_boxed_133_ = lean_unbox(v_includeStop_132_);
v_res_134_ = l_Lean_Syntax_Range_contains(v_r_130_, v_pos_131_, v_includeStop_boxed_133_);
lean_dec(v_pos_131_);
lean_dec_ref(v_r_130_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_includes(lean_object* v_super_136_, lean_object* v_sub_137_, uint8_t v_includeSuperStop_138_, uint8_t v_includeSubStop_139_){
_start:
{
lean_object* v_start_140_; lean_object* v_stop_141_; lean_object* v_start_142_; lean_object* v_stop_143_; uint8_t v___y_150_; uint8_t v___x_152_; 
v_start_140_ = lean_ctor_get(v_super_136_, 0);
v_stop_141_ = lean_ctor_get(v_super_136_, 1);
v_start_142_ = lean_ctor_get(v_sub_137_, 0);
v_stop_143_ = lean_ctor_get(v_sub_137_, 1);
v___x_152_ = lean_nat_dec_le(v_start_140_, v_start_142_);
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
if (v_includeSuperStop_138_ == 0)
{
v___y_150_ = v_includeSuperStop_138_;
goto v___jp_149_;
}
else
{
if (v_includeSubStop_139_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_nat_add(v_stop_141_, v___x_153_);
v___x_155_ = lean_nat_dec_le(v_stop_143_, v___x_154_);
lean_dec(v___x_154_);
return v___x_155_;
}
else
{
uint8_t v___x_156_; 
v___x_156_ = 0;
v___y_150_ = v___x_156_;
goto v___jp_149_;
}
}
}
v___jp_144_:
{
if (v_includeSubStop_139_ == 0)
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v_stop_143_, v_stop_141_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = lean_nat_add(v_stop_143_, v___x_146_);
v___x_148_ = lean_nat_dec_le(v___x_147_, v_stop_141_);
lean_dec(v___x_147_);
return v___x_148_;
}
}
v___jp_149_:
{
if (v_includeSuperStop_138_ == 0)
{
goto v___jp_144_;
}
else
{
if (v___y_150_ == 0)
{
uint8_t v___x_151_; 
v___x_151_ = lean_nat_dec_le(v_stop_143_, v_stop_141_);
return v___x_151_;
}
else
{
goto v___jp_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_includes___boxed(lean_object* v_super_157_, lean_object* v_sub_158_, lean_object* v_includeSuperStop_159_, lean_object* v_includeSubStop_160_){
_start:
{
uint8_t v_includeSuperStop_boxed_161_; uint8_t v_includeSubStop_boxed_162_; uint8_t v_res_163_; lean_object* v_r_164_; 
v_includeSuperStop_boxed_161_ = lean_unbox(v_includeSuperStop_159_);
v_includeSubStop_boxed_162_ = lean_unbox(v_includeSubStop_160_);
v_res_163_ = l_Lean_Syntax_Range_includes(v_super_157_, v_sub_158_, v_includeSuperStop_boxed_161_, v_includeSubStop_boxed_162_);
lean_dec_ref(v_sub_158_);
lean_dec_ref(v_super_157_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Range_overlaps(lean_object* v_first_165_, lean_object* v_second_166_, uint8_t v_includeFirstStop_167_, uint8_t v_includeSecondStop_168_){
_start:
{
uint8_t v___y_170_; 
if (v_includeFirstStop_167_ == 0)
{
lean_object* v_start_179_; lean_object* v_stop_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_start_179_ = lean_ctor_get(v_second_166_, 0);
v_stop_180_ = lean_ctor_get(v_first_165_, 1);
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_start_179_, v___x_181_);
v___x_183_ = lean_nat_dec_le(v___x_182_, v_stop_180_);
lean_dec(v___x_182_);
v___y_170_ = v___x_183_;
goto v___jp_169_;
}
else
{
lean_object* v_start_184_; lean_object* v_stop_185_; uint8_t v___x_186_; 
v_start_184_ = lean_ctor_get(v_second_166_, 0);
v_stop_185_ = lean_ctor_get(v_first_165_, 1);
v___x_186_ = lean_nat_dec_le(v_start_184_, v_stop_185_);
v___y_170_ = v___x_186_;
goto v___jp_169_;
}
v___jp_169_:
{
if (v___y_170_ == 0)
{
return v___y_170_;
}
else
{
if (v_includeSecondStop_168_ == 0)
{
lean_object* v_start_171_; lean_object* v_stop_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_start_171_ = lean_ctor_get(v_first_165_, 0);
v_stop_172_ = lean_ctor_get(v_second_166_, 1);
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_start_171_, v___x_173_);
v___x_175_ = lean_nat_dec_le(v___x_174_, v_stop_172_);
lean_dec(v___x_174_);
return v___x_175_;
}
else
{
lean_object* v_start_176_; lean_object* v_stop_177_; uint8_t v___x_178_; 
v_start_176_ = lean_ctor_get(v_first_165_, 0);
v_stop_177_ = lean_ctor_get(v_second_166_, 1);
v___x_178_ = lean_nat_dec_le(v_start_176_, v_stop_177_);
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_overlaps___boxed(lean_object* v_first_187_, lean_object* v_second_188_, lean_object* v_includeFirstStop_189_, lean_object* v_includeSecondStop_190_){
_start:
{
uint8_t v_includeFirstStop_boxed_191_; uint8_t v_includeSecondStop_boxed_192_; uint8_t v_res_193_; lean_object* v_r_194_; 
v_includeFirstStop_boxed_191_ = lean_unbox(v_includeFirstStop_189_);
v_includeSecondStop_boxed_192_ = lean_unbox(v_includeSecondStop_190_);
v_res_193_ = l_Lean_Syntax_Range_overlaps(v_first_187_, v_second_188_, v_includeFirstStop_boxed_191_, v_includeSecondStop_boxed_192_);
lean_dec_ref(v_second_188_);
lean_dec_ref(v_first_187_);
v_r_194_ = lean_box(v_res_193_);
return v_r_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize(lean_object* v_r_195_){
_start:
{
lean_object* v_start_196_; lean_object* v_stop_197_; lean_object* v___x_198_; 
v_start_196_ = lean_ctor_get(v_r_195_, 0);
v_stop_197_ = lean_ctor_get(v_r_195_, 1);
v___x_198_ = lean_nat_sub(v_stop_197_, v_start_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_bsize___boxed(lean_object* v_r_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Syntax_Range_bsize(v_r_199_);
lean_dec_ref(v_r_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_updateTrailing(lean_object* v_trailing_201_, lean_object* v_x_202_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
lean_object* v_leading_203_; lean_object* v_pos_204_; lean_object* v_endPos_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_leading_203_ = lean_ctor_get(v_x_202_, 0);
v_pos_204_ = lean_ctor_get(v_x_202_, 1);
v_endPos_205_ = lean_ctor_get(v_x_202_, 3);
v_isSharedCheck_212_ = !lean_is_exclusive(v_x_202_);
if (v_isSharedCheck_212_ == 0)
{
lean_object* v_unused_213_; 
v_unused_213_ = lean_ctor_get(v_x_202_, 2);
lean_dec(v_unused_213_);
v___x_207_ = v_x_202_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_endPos_205_);
lean_inc(v_pos_204_);
lean_inc(v_leading_203_);
lean_dec(v_x_202_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 2, v_trailing_201_);
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_leading_203_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_pos_204_);
lean_ctor_set(v_reuseFailAlloc_211_, 2, v_trailing_201_);
lean_ctor_set(v_reuseFailAlloc_211_, 3, v_endPos_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
else
{
lean_dec_ref(v_trailing_201_);
return v_x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f(uint8_t v_canonicalOnly_214_, lean_object* v_info_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_SourceInfo_getPos_x3f(v_info_215_, v_canonicalOnly_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_val_218_; lean_object* v___x_219_; 
v_val_218_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_val_218_);
lean_dec_ref_known(v___x_216_, 1);
v___x_219_ = l_Lean_SourceInfo_getTailPos_x3f(v_info_215_, v_canonicalOnly_214_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v___x_220_; 
lean_dec(v_val_218_);
v___x_220_ = lean_box(0);
return v___x_220_;
}
else
{
lean_object* v_val_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_229_; 
v_val_221_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_229_ == 0)
{
v___x_223_ = v___x_219_;
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_val_221_);
lean_dec(v___x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_229_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_227_; 
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_val_218_);
lean_ctor_set(v___x_225_, 1, v_val_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_227_ = v___x_223_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRange_x3f___boxed(lean_object* v_canonicalOnly_230_, lean_object* v_info_231_){
_start:
{
uint8_t v_canonicalOnly_boxed_232_; lean_object* v_res_233_; 
v_canonicalOnly_boxed_232_ = lean_unbox(v_canonicalOnly_230_);
v_res_233_ = l_Lean_SourceInfo_getRange_x3f(v_canonicalOnly_boxed_232_, v_info_231_);
lean_dec(v_info_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f(uint8_t v_canonicalOnly_234_, lean_object* v_info_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_SourceInfo_getPos_x3f(v_info_235_, v_canonicalOnly_234_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v___x_237_; 
v___x_237_ = lean_box(0);
return v___x_237_;
}
else
{
lean_object* v_val_238_; lean_object* v___x_239_; 
v_val_238_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v___x_236_, 1);
v___x_239_ = l_Lean_SourceInfo_getTrailingTailPos_x3f(v_info_235_, v_canonicalOnly_234_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v___x_240_; 
lean_dec(v_val_238_);
v___x_240_ = lean_box(0);
return v___x_240_;
}
else
{
lean_object* v_val_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_249_; 
v_val_241_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_249_ == 0)
{
v___x_243_ = v___x_239_;
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_val_241_);
lean_dec(v___x_239_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_249_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_247_; 
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v_val_238_);
lean_ctor_set(v___x_245_, 1, v_val_241_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_247_ = v___x_243_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_getRangeWithTrailing_x3f___boxed(lean_object* v_canonicalOnly_250_, lean_object* v_info_251_){
_start:
{
uint8_t v_canonicalOnly_boxed_252_; lean_object* v_res_253_; 
v_canonicalOnly_boxed_252_ = lean_unbox(v_canonicalOnly_250_);
v_res_253_ = l_Lean_SourceInfo_getRangeWithTrailing_x3f(v_canonicalOnly_boxed_252_, v_info_251_);
lean_dec(v_info_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_SourceInfo_nonCanonicalSynthetic(lean_object* v_x_254_){
_start:
{
switch(lean_obj_tag(v_x_254_))
{
case 0:
{
lean_object* v_pos_255_; lean_object* v_endPos_256_; uint8_t v___x_257_; lean_object* v___x_258_; 
v_pos_255_ = lean_ctor_get(v_x_254_, 1);
lean_inc(v_pos_255_);
v_endPos_256_ = lean_ctor_get(v_x_254_, 3);
lean_inc(v_endPos_256_);
lean_dec_ref_known(v_x_254_, 4);
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_258_, 0, v_pos_255_);
lean_ctor_set(v___x_258_, 1, v_endPos_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*2, v___x_257_);
return v___x_258_;
}
case 1:
{
lean_object* v_pos_259_; lean_object* v_endPos_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_pos_259_ = lean_ctor_get(v_x_254_, 0);
v_endPos_260_ = lean_ctor_get(v_x_254_, 1);
v_isSharedCheck_268_ = !lean_is_exclusive(v_x_254_);
if (v_isSharedCheck_268_ == 0)
{
v___x_262_ = v_x_254_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_endPos_260_);
lean_inc(v_pos_259_);
lean_dec(v_x_254_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
uint8_t v___x_264_; lean_object* v___x_266_; 
v___x_264_ = 0;
if (v_isShared_263_ == 0)
{
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_pos_259_);
lean_ctor_set(v_reuseFailAlloc_267_, 1, v_endPos_260_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_ctor_set_uint8(v___x_266_, sizeof(void*)*2, v___x_264_);
return v___x_266_;
}
}
}
default: 
{
return v_x_254_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqSourceInfo__lean_beq(lean_object* v_x_269_, lean_object* v_x_270_){
_start:
{
switch(lean_obj_tag(v_x_269_))
{
case 0:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_object* v_leading_271_; lean_object* v_pos_272_; lean_object* v_trailing_273_; lean_object* v_endPos_274_; lean_object* v_leading_275_; lean_object* v_pos_276_; lean_object* v_trailing_277_; lean_object* v_endPos_278_; uint8_t v___x_279_; 
v_leading_271_ = lean_ctor_get(v_x_269_, 0);
lean_inc_ref(v_leading_271_);
v_pos_272_ = lean_ctor_get(v_x_269_, 1);
lean_inc(v_pos_272_);
v_trailing_273_ = lean_ctor_get(v_x_269_, 2);
lean_inc_ref(v_trailing_273_);
v_endPos_274_ = lean_ctor_get(v_x_269_, 3);
lean_inc(v_endPos_274_);
lean_dec_ref_known(v_x_269_, 4);
v_leading_275_ = lean_ctor_get(v_x_270_, 0);
lean_inc_ref(v_leading_275_);
v_pos_276_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_pos_276_);
v_trailing_277_ = lean_ctor_get(v_x_270_, 2);
lean_inc_ref(v_trailing_277_);
v_endPos_278_ = lean_ctor_get(v_x_270_, 3);
lean_inc(v_endPos_278_);
lean_dec_ref_known(v_x_270_, 4);
v___x_279_ = l_Substring_Raw_beq(v_leading_271_, v_leading_275_);
if (v___x_279_ == 0)
{
lean_dec(v_endPos_278_);
lean_dec_ref(v_trailing_277_);
lean_dec(v_pos_276_);
lean_dec(v_endPos_274_);
lean_dec_ref(v_trailing_273_);
lean_dec(v_pos_272_);
return v___x_279_;
}
else
{
uint8_t v_decide_280_; 
v_decide_280_ = lean_nat_dec_eq(v_pos_272_, v_pos_276_);
lean_dec(v_pos_276_);
lean_dec(v_pos_272_);
if (v_decide_280_ == 0)
{
lean_dec(v_endPos_278_);
lean_dec_ref(v_trailing_277_);
lean_dec(v_endPos_274_);
lean_dec_ref(v_trailing_273_);
return v_decide_280_;
}
else
{
uint8_t v___x_281_; 
v___x_281_ = l_Substring_Raw_beq(v_trailing_273_, v_trailing_277_);
if (v___x_281_ == 0)
{
lean_dec(v_endPos_278_);
lean_dec(v_endPos_274_);
return v___x_281_;
}
else
{
uint8_t v_decide_282_; 
v_decide_282_ = lean_nat_dec_eq(v_endPos_274_, v_endPos_278_);
lean_dec(v_endPos_278_);
lean_dec(v_endPos_274_);
return v_decide_282_;
}
}
}
}
else
{
uint8_t v___x_283_; 
lean_dec_ref_known(v_x_269_, 4);
lean_dec(v_x_270_);
v___x_283_ = 0;
return v___x_283_;
}
}
case 1:
{
if (lean_obj_tag(v_x_270_) == 1)
{
lean_object* v_pos_284_; lean_object* v_endPos_285_; uint8_t v_canonical_286_; lean_object* v_pos_287_; lean_object* v_endPos_288_; uint8_t v_canonical_289_; uint8_t v_decide_290_; 
v_pos_284_ = lean_ctor_get(v_x_269_, 0);
lean_inc(v_pos_284_);
v_endPos_285_ = lean_ctor_get(v_x_269_, 1);
lean_inc(v_endPos_285_);
v_canonical_286_ = lean_ctor_get_uint8(v_x_269_, sizeof(void*)*2);
lean_dec_ref_known(v_x_269_, 2);
v_pos_287_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_pos_287_);
v_endPos_288_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_endPos_288_);
v_canonical_289_ = lean_ctor_get_uint8(v_x_270_, sizeof(void*)*2);
lean_dec_ref_known(v_x_270_, 2);
v_decide_290_ = lean_nat_dec_eq(v_pos_284_, v_pos_287_);
lean_dec(v_pos_287_);
lean_dec(v_pos_284_);
if (v_decide_290_ == 0)
{
lean_dec(v_endPos_288_);
lean_dec(v_endPos_285_);
return v_decide_290_;
}
else
{
uint8_t v_decide_291_; 
v_decide_291_ = lean_nat_dec_eq(v_endPos_285_, v_endPos_288_);
lean_dec(v_endPos_288_);
lean_dec(v_endPos_285_);
if (v_decide_291_ == 0)
{
return v_decide_291_;
}
else
{
if (v_canonical_289_ == 0)
{
if (v_canonical_286_ == 0)
{
return v_decide_291_;
}
else
{
return v_canonical_289_;
}
}
else
{
return v_canonical_286_;
}
}
}
}
else
{
uint8_t v___x_292_; 
lean_dec_ref_known(v_x_269_, 2);
lean_dec(v_x_270_);
v___x_292_ = 0;
return v___x_292_;
}
}
default: 
{
if (lean_obj_tag(v_x_270_) == 2)
{
uint8_t v___x_293_; 
v___x_293_ = 1;
return v___x_293_;
}
else
{
uint8_t v___x_294_; 
lean_dec(v_x_270_);
v___x_294_ = 0;
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqSourceInfo__lean_beq___boxed(lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
uint8_t v_res_297_; lean_object* v_r_298_; 
v_res_297_ = l_Lean_instBEqSourceInfo__lean_beq(v_x_295_, v_x_296_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing___redArg___boxed(lean_object* v___dummy_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_unreachIsNodeMissing___redArg();
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeMissing(lean_object* v_00_u03b2_304_, lean_object* v_a_305_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___redArg___boxed(lean_object* v___dummy_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_unreachIsNodeAtom___redArg();
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom(lean_object* v_00_u03b2_309_, lean_object* v_info_310_, lean_object* v_val_311_, lean_object* v_a_312_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeAtom___boxed(lean_object* v_00_u03b2_313_, lean_object* v_info_314_, lean_object* v_val_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_unreachIsNodeAtom(v_00_u03b2_313_, v_info_314_, v_val_315_, v_a_316_);
lean_dec_ref(v_val_315_);
lean_dec(v_info_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___redArg___boxed(lean_object* v___dummy_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_unreachIsNodeIdent___redArg();
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent(lean_object* v_00_u03b2_321_, lean_object* v_info_322_, lean_object* v_rawVal_323_, lean_object* v_val_324_, lean_object* v_preresolved_325_, lean_object* v_a_326_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_Lean_unreachIsNodeIdent___boxed(lean_object* v_00_u03b2_327_, lean_object* v_info_328_, lean_object* v_rawVal_329_, lean_object* v_val_330_, lean_object* v_preresolved_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_unreachIsNodeIdent(v_00_u03b2_327_, v_info_328_, v_rawVal_329_, v_val_330_, v_preresolved_331_, v_a_332_);
lean_dec(v_preresolved_331_);
lean_dec(v_val_330_);
lean_dec_ref(v_rawVal_329_);
lean_dec(v_info_328_);
return v_res_333_;
}
}
LEAN_EXPORT uint8_t l_Lean_isLitKind(lean_object* v_k_349_){
_start:
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l_Lean_isLitKind___closed__1));
v___x_351_ = lean_name_eq(v_k_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l_Lean_isLitKind___closed__3));
v___x_353_ = lean_name_eq(v_k_349_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = ((lean_object*)(l_Lean_isLitKind___closed__5));
v___x_355_ = lean_name_eq(v_k_349_, v___x_354_);
if (v___x_355_ == 0)
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = ((lean_object*)(l_Lean_isLitKind___closed__7));
v___x_357_ = lean_name_eq(v_k_349_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_isLitKind___closed__9));
v___x_359_ = lean_name_eq(v_k_349_, v___x_358_);
return v___x_359_;
}
else
{
return v___x_357_;
}
}
else
{
return v___x_355_;
}
}
else
{
return v___x_353_;
}
}
else
{
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLitKind___boxed(lean_object* v_k_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lean_isLitKind(v_k_360_);
lean_dec(v_k_360_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind(lean_object* v_n_363_){
_start:
{
lean_object* v_kind_364_; 
v_kind_364_ = lean_ctor_get(v_n_363_, 1);
lean_inc(v_kind_364_);
return v_kind_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getKind___boxed(lean_object* v_n_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_SyntaxNode_getKind(v_n_365_);
lean_dec(v_n_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs___redArg(lean_object* v_n_367_, lean_object* v_fn_368_){
_start:
{
lean_object* v_args_369_; lean_object* v___x_370_; 
v_args_369_ = lean_ctor_get(v_n_367_, 2);
lean_inc_ref(v_args_369_);
lean_dec(v_n_367_);
v___x_370_ = lean_apply_1(v_fn_368_, v_args_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_withArgs(lean_object* v_00_u03b2_371_, lean_object* v_n_372_, lean_object* v_fn_373_){
_start:
{
lean_object* v_args_374_; lean_object* v___x_375_; 
v_args_374_ = lean_ctor_get(v_n_372_, 2);
lean_inc_ref(v_args_374_);
lean_dec(v_n_372_);
v___x_375_ = lean_apply_1(v_fn_373_, v_args_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs(lean_object* v_n_376_){
_start:
{
lean_object* v_args_377_; lean_object* v___x_378_; 
v_args_377_ = lean_ctor_get(v_n_376_, 2);
v___x_378_ = lean_array_get_size(v_args_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getNumArgs___boxed(lean_object* v_n_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_SyntaxNode_getNumArgs(v_n_379_);
lean_dec(v_n_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg(lean_object* v_n_381_, lean_object* v_i_382_){
_start:
{
lean_object* v_args_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_args_383_ = lean_ctor_get(v_n_381_, 2);
v___x_384_ = lean_box(0);
v___x_385_ = lean_array_get_borrowed(v___x_384_, v_args_383_, v_i_382_);
lean_inc(v___x_385_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArg___boxed(lean_object* v_n_386_, lean_object* v_i_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_SyntaxNode_getArg(v_n_386_, v_i_387_);
lean_dec(v_i_387_);
lean_dec(v_n_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs(lean_object* v_n_389_){
_start:
{
lean_object* v_args_390_; 
v_args_390_ = lean_ctor_get(v_n_389_, 2);
lean_inc_ref(v_args_390_);
return v_args_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getArgs___boxed(lean_object* v_n_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_SyntaxNode_getArgs(v_n_391_);
lean_dec(v_n_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_modifyArgs(lean_object* v_n_393_, lean_object* v_fn_394_){
_start:
{
lean_object* v_info_395_; lean_object* v_kind_396_; lean_object* v_args_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_405_; 
v_info_395_ = lean_ctor_get(v_n_393_, 0);
v_kind_396_ = lean_ctor_get(v_n_393_, 1);
v_args_397_ = lean_ctor_get(v_n_393_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_n_393_);
if (v_isSharedCheck_405_ == 0)
{
v___x_399_ = v_n_393_;
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_args_397_);
lean_inc(v_kind_396_);
lean_inc(v_info_395_);
lean_dec(v_n_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_405_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_apply_1(v_fn_394_, v_args_397_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 2, v___x_401_);
v___x_403_ = v___x_399_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_info_395_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_kind_396_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0(lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
if (lean_obj_tag(v_x_406_) == 0)
{
if (lean_obj_tag(v_x_407_) == 0)
{
uint8_t v___x_408_; 
v___x_408_ = 1;
return v___x_408_;
}
else
{
uint8_t v___x_409_; 
v___x_409_ = 0;
return v___x_409_;
}
}
else
{
if (lean_obj_tag(v_x_407_) == 0)
{
uint8_t v___x_410_; 
v___x_410_ = 0;
return v___x_410_;
}
else
{
lean_object* v_val_411_; lean_object* v_val_412_; uint8_t v___x_413_; 
v_val_411_ = lean_ctor_get(v_x_406_, 0);
v_val_412_ = lean_ctor_get(v_x_407_, 0);
v___x_413_ = l_Lean_Syntax_instBEqRange_beq(v_val_411_, v_val_412_);
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0___boxed(lean_object* v_x_414_, lean_object* v_x_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0(v_x_414_, v_x_415_);
lean_dec(v_x_415_);
lean_dec(v_x_414_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(lean_object* v_x_418_, lean_object* v_x_419_){
_start:
{
if (lean_obj_tag(v_x_418_) == 0)
{
if (lean_obj_tag(v_x_419_) == 0)
{
uint8_t v___x_420_; 
v___x_420_ = 1;
return v___x_420_;
}
else
{
uint8_t v___x_421_; 
v___x_421_ = 0;
return v___x_421_;
}
}
else
{
if (lean_obj_tag(v_x_419_) == 0)
{
uint8_t v___x_422_; 
v___x_422_ = 0;
return v___x_422_;
}
else
{
lean_object* v_head_423_; lean_object* v_tail_424_; lean_object* v_head_425_; lean_object* v_tail_426_; uint8_t v___x_427_; 
v_head_423_ = lean_ctor_get(v_x_418_, 0);
v_tail_424_ = lean_ctor_get(v_x_418_, 1);
v_head_425_ = lean_ctor_get(v_x_419_, 0);
v_tail_426_ = lean_ctor_get(v_x_419_, 1);
v___x_427_ = l_Lean_Syntax_instBEqPreresolved_beq(v_head_423_, v_head_425_);
if (v___x_427_ == 0)
{
return v___x_427_;
}
else
{
v_x_418_ = v_tail_424_;
v_x_419_ = v_tail_426_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2___boxed(lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
uint8_t v_res_431_; lean_object* v_r_432_; 
v_res_431_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_x_429_, v_x_430_);
lean_dec(v_x_430_);
lean_dec(v_x_429_);
v_r_432_ = lean_box(v_res_431_);
return v_r_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEq(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
switch(lean_obj_tag(v_x_433_))
{
case 0:
{
if (lean_obj_tag(v_x_434_) == 0)
{
uint8_t v___x_435_; 
v___x_435_ = 1;
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
lean_dec(v_x_434_);
v___x_436_ = 0;
return v___x_436_;
}
}
case 1:
{
if (lean_obj_tag(v_x_434_) == 1)
{
lean_object* v_info_437_; lean_object* v_kind_438_; lean_object* v_args_439_; lean_object* v_info_440_; lean_object* v_kind_441_; lean_object* v_args_442_; uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_info_437_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_info_437_);
v_kind_438_ = lean_ctor_get(v_x_433_, 1);
lean_inc(v_kind_438_);
v_args_439_ = lean_ctor_get(v_x_433_, 2);
lean_inc_ref(v_args_439_);
lean_dec_ref_known(v_x_433_, 3);
v_info_440_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_info_440_);
v_kind_441_ = lean_ctor_get(v_x_434_, 1);
lean_inc(v_kind_441_);
v_args_442_ = lean_ctor_get(v_x_434_, 2);
lean_inc_ref(v_args_442_);
lean_dec_ref_known(v_x_434_, 3);
v___x_443_ = 0;
v___x_444_ = l_Lean_SourceInfo_getRange_x3f(v___x_443_, v_info_437_);
lean_dec(v_info_437_);
v___x_445_ = l_Lean_SourceInfo_getRange_x3f(v___x_443_, v_info_440_);
lean_dec(v_info_440_);
v___x_446_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0(v___x_444_, v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_444_);
if (v___x_446_ == 0)
{
lean_dec_ref(v_args_442_);
lean_dec(v_kind_441_);
lean_dec_ref(v_args_439_);
lean_dec(v_kind_438_);
return v___x_446_;
}
else
{
uint8_t v___x_447_; 
v___x_447_ = lean_name_eq(v_kind_438_, v_kind_441_);
lean_dec(v_kind_441_);
lean_dec(v_kind_438_);
if (v___x_447_ == 0)
{
lean_dec_ref(v_args_442_);
lean_dec_ref(v_args_439_);
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_array_get_size(v_args_439_);
v___x_449_ = lean_array_get_size(v_args_442_);
v___x_450_ = lean_nat_dec_eq(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_dec_ref(v_args_442_);
lean_dec_ref(v_args_439_);
return v___x_450_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___redArg(v_args_439_, v_args_442_, v___x_448_);
lean_dec_ref(v_args_442_);
lean_dec_ref(v_args_439_);
return v___x_451_;
}
}
}
}
else
{
uint8_t v___x_452_; 
lean_dec_ref_known(v_x_433_, 3);
lean_dec(v_x_434_);
v___x_452_ = 0;
return v___x_452_;
}
}
case 2:
{
if (lean_obj_tag(v_x_434_) == 2)
{
lean_object* v_info_453_; lean_object* v_val_454_; lean_object* v_info_455_; lean_object* v_val_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; 
v_info_453_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_info_453_);
v_val_454_ = lean_ctor_get(v_x_433_, 1);
lean_inc_ref(v_val_454_);
lean_dec_ref_known(v_x_433_, 2);
v_info_455_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_info_455_);
v_val_456_ = lean_ctor_get(v_x_434_, 1);
lean_inc_ref(v_val_456_);
lean_dec_ref_known(v_x_434_, 2);
v___x_457_ = 0;
v___x_458_ = l_Lean_SourceInfo_getRange_x3f(v___x_457_, v_info_453_);
lean_dec(v_info_453_);
v___x_459_ = l_Lean_SourceInfo_getRange_x3f(v___x_457_, v_info_455_);
lean_dec(v_info_455_);
v___x_460_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0(v___x_458_, v___x_459_);
lean_dec(v___x_459_);
lean_dec(v___x_458_);
if (v___x_460_ == 0)
{
lean_dec_ref(v_val_456_);
lean_dec_ref(v_val_454_);
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = lean_string_dec_eq(v_val_454_, v_val_456_);
lean_dec_ref(v_val_456_);
lean_dec_ref(v_val_454_);
return v___x_461_;
}
}
else
{
uint8_t v___x_462_; 
lean_dec_ref_known(v_x_433_, 2);
lean_dec(v_x_434_);
v___x_462_ = 0;
return v___x_462_;
}
}
default: 
{
if (lean_obj_tag(v_x_434_) == 3)
{
lean_object* v_info_463_; lean_object* v_rawVal_464_; lean_object* v_val_465_; lean_object* v_preresolved_466_; lean_object* v_info_467_; lean_object* v_rawVal_468_; lean_object* v_val_469_; lean_object* v_preresolved_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v_info_463_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_info_463_);
v_rawVal_464_ = lean_ctor_get(v_x_433_, 1);
lean_inc_ref(v_rawVal_464_);
v_val_465_ = lean_ctor_get(v_x_433_, 2);
lean_inc(v_val_465_);
v_preresolved_466_ = lean_ctor_get(v_x_433_, 3);
lean_inc(v_preresolved_466_);
lean_dec_ref_known(v_x_433_, 4);
v_info_467_ = lean_ctor_get(v_x_434_, 0);
lean_inc(v_info_467_);
v_rawVal_468_ = lean_ctor_get(v_x_434_, 1);
lean_inc_ref(v_rawVal_468_);
v_val_469_ = lean_ctor_get(v_x_434_, 2);
lean_inc(v_val_469_);
v_preresolved_470_ = lean_ctor_get(v_x_434_, 3);
lean_inc(v_preresolved_470_);
lean_dec_ref_known(v_x_434_, 4);
v___x_471_ = 0;
v___x_472_ = l_Lean_SourceInfo_getRange_x3f(v___x_471_, v_info_463_);
lean_dec(v_info_463_);
v___x_473_ = l_Lean_SourceInfo_getRange_x3f(v___x_471_, v_info_467_);
lean_dec(v_info_467_);
v___x_474_ = l_instBEqOption_beq___at___00Lean_Syntax_structRangeEq_spec__0(v___x_472_, v___x_473_);
lean_dec(v___x_473_);
lean_dec(v___x_472_);
if (v___x_474_ == 0)
{
lean_dec(v_preresolved_470_);
lean_dec(v_val_469_);
lean_dec_ref(v_rawVal_468_);
lean_dec(v_preresolved_466_);
lean_dec(v_val_465_);
lean_dec_ref(v_rawVal_464_);
return v___x_474_;
}
else
{
uint8_t v___x_475_; 
v___x_475_ = l_Substring_Raw_beq(v_rawVal_464_, v_rawVal_468_);
if (v___x_475_ == 0)
{
lean_dec(v_preresolved_470_);
lean_dec(v_val_469_);
lean_dec(v_preresolved_466_);
lean_dec(v_val_465_);
return v___x_475_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_name_eq(v_val_465_, v_val_469_);
lean_dec(v_val_469_);
lean_dec(v_val_465_);
if (v___x_476_ == 0)
{
lean_dec(v_preresolved_470_);
lean_dec(v_preresolved_466_);
return v___x_476_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_466_, v_preresolved_470_);
lean_dec(v_preresolved_470_);
lean_dec(v_preresolved_466_);
return v___x_477_;
}
}
}
}
else
{
uint8_t v___x_478_; 
lean_dec_ref_known(v_x_433_, 4);
lean_dec(v_x_434_);
v___x_478_ = 0;
return v___x_478_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___redArg(lean_object* v_xs_479_, lean_object* v_ys_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_zero_482_; uint8_t v_isZero_483_; 
v_zero_482_ = lean_unsigned_to_nat(0u);
v_isZero_483_ = lean_nat_dec_eq(v_x_481_, v_zero_482_);
if (v_isZero_483_ == 1)
{
lean_dec(v_x_481_);
return v_isZero_483_;
}
else
{
lean_object* v_one_484_; lean_object* v_n_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_one_484_ = lean_unsigned_to_nat(1u);
v_n_485_ = lean_nat_sub(v_x_481_, v_one_484_);
lean_dec(v_x_481_);
v___x_486_ = lean_array_fget_borrowed(v_xs_479_, v_n_485_);
v___x_487_ = lean_array_fget_borrowed(v_ys_480_, v_n_485_);
lean_inc(v___x_487_);
lean_inc(v___x_486_);
v___x_488_ = l_Lean_Syntax_structRangeEq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_dec(v_n_485_);
return v___x_488_;
}
else
{
v_x_481_ = v_n_485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___redArg___boxed(lean_object* v_xs_490_, lean_object* v_ys_491_, lean_object* v_x_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___redArg(v_xs_490_, v_ys_491_, v_x_492_);
lean_dec_ref(v_ys_491_);
lean_dec_ref(v_xs_490_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEq___boxed(lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = l_Lean_Syntax_structRangeEq(v_x_495_, v_x_496_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1(lean_object* v_xs_499_, lean_object* v_ys_500_, lean_object* v_hsz_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
uint8_t v___x_504_; 
v___x_504_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___redArg(v_xs_499_, v_ys_500_, v_x_502_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1___boxed(lean_object* v_xs_505_, lean_object* v_ys_506_, lean_object* v_hsz_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_Array_isEqvAux___at___00Lean_Syntax_structRangeEq_spec__1(v_xs_505_, v_ys_506_, v_hsz_507_, v_x_508_, v_x_509_);
lean_dec_ref(v_ys_506_);
lean_dec_ref(v_xs_505_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(uint8_t v___x_512_, lean_object* v_x_513_){
_start:
{
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed(lean_object* v___x_514_, lean_object* v_x_515_){
_start:
{
uint8_t v___x_113__boxed_516_; uint8_t v_res_517_; lean_object* v_r_518_; 
v___x_113__boxed_516_ = lean_unbox(v___x_514_);
v_res_517_ = l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0(v___x_113__boxed_516_, v_x_515_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_structRangeEqWithTraceReuse(lean_object* v_opts_528_, lean_object* v_stx1_529_, lean_object* v_stx2_530_){
_start:
{
uint8_t v___x_531_; uint8_t v___x_532_; 
lean_inc(v_stx2_530_);
lean_inc(v_stx1_529_);
v___x_531_ = l_Lean_Syntax_structRangeEq(v_stx1_529_, v_stx2_530_);
v___x_532_ = 1;
if (v___x_531_ == 0)
{
lean_object* v_map_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_map_533_ = lean_ctor_get(v_opts_528_, 0);
v___x_534_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3));
v___x_535_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_533_, v___x_534_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_dec(v_stx2_530_);
lean_dec(v_stx1_529_);
return v___x_531_;
}
else
{
lean_object* v_val_536_; 
v_val_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_val_536_);
lean_dec_ref_known(v___x_535_, 1);
if (lean_obj_tag(v_val_536_) == 1)
{
uint8_t v_v_537_; 
v_v_537_ = lean_ctor_get_uint8(v_val_536_, 0);
lean_dec_ref_known(v_val_536_, 0);
if (v_v_537_ == 0)
{
lean_dec(v_stx2_530_);
lean_dec(v_stx1_529_);
return v___x_531_;
}
else
{
lean_object* v___x_538_; lean_object* v___f_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_538_ = lean_box(v___x_531_);
v___f_539_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_539_, 0, v___x_538_);
v___x_540_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4));
v___x_541_ = lean_box(0);
v___x_542_ = l_Lean_Syntax_formatStx(v_stx1_529_, v___x_541_, v___x_532_);
v___x_543_ = l_Std_Format_defWidth;
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = l_Std_Format_pretty(v___x_542_, v___x_543_, v___x_544_, v___x_544_);
v___x_546_ = lean_string_append(v___x_540_, v___x_545_);
lean_dec_ref(v___x_545_);
v___x_547_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_548_ = lean_string_append(v___x_546_, v___x_547_);
v___x_549_ = l_Lean_Syntax_formatStx(v_stx2_530_, v___x_541_, v___x_532_);
v___x_550_ = l_Std_Format_pretty(v___x_549_, v___x_543_, v___x_544_, v___x_544_);
v___x_551_ = lean_string_append(v___x_548_, v___x_550_);
lean_dec_ref(v___x_550_);
v___x_552_ = lean_dbg_trace(v___x_551_, v___f_539_);
v___x_553_ = lean_unbox(v___x_552_);
lean_dec(v___x_552_);
return v___x_553_;
}
}
else
{
lean_dec(v_val_536_);
lean_dec(v_stx2_530_);
lean_dec(v_stx1_529_);
return v___x_531_;
}
}
}
else
{
lean_dec(v_stx2_530_);
lean_dec(v_stx1_529_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_structRangeEqWithTraceReuse___boxed(lean_object* v_opts_554_, lean_object* v_stx1_555_, lean_object* v_stx2_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lean_Syntax_structRangeEqWithTraceReuse(v_opts_554_, v_stx1_555_, v_stx2_556_);
lean_dec_ref(v_opts_554_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfo(lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
switch(lean_obj_tag(v_x_559_))
{
case 0:
{
if (lean_obj_tag(v_x_560_) == 0)
{
uint8_t v___x_561_; 
v___x_561_ = 1;
return v___x_561_;
}
else
{
uint8_t v___x_562_; 
lean_dec(v_x_560_);
v___x_562_ = 0;
return v___x_562_;
}
}
case 1:
{
if (lean_obj_tag(v_x_560_) == 1)
{
lean_object* v_info_563_; lean_object* v_kind_564_; lean_object* v_args_565_; lean_object* v_info_566_; lean_object* v_kind_567_; lean_object* v_args_568_; uint8_t v___x_569_; 
v_info_563_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_info_563_);
v_kind_564_ = lean_ctor_get(v_x_559_, 1);
lean_inc(v_kind_564_);
v_args_565_ = lean_ctor_get(v_x_559_, 2);
lean_inc_ref(v_args_565_);
lean_dec_ref_known(v_x_559_, 3);
v_info_566_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_info_566_);
v_kind_567_ = lean_ctor_get(v_x_560_, 1);
lean_inc(v_kind_567_);
v_args_568_ = lean_ctor_get(v_x_560_, 2);
lean_inc_ref(v_args_568_);
lean_dec_ref_known(v_x_560_, 3);
v___x_569_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_563_, v_info_566_);
if (v___x_569_ == 0)
{
lean_dec_ref(v_args_568_);
lean_dec(v_kind_567_);
lean_dec_ref(v_args_565_);
lean_dec(v_kind_564_);
return v___x_569_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = lean_name_eq(v_kind_564_, v_kind_567_);
lean_dec(v_kind_567_);
lean_dec(v_kind_564_);
if (v___x_570_ == 0)
{
lean_dec_ref(v_args_568_);
lean_dec_ref(v_args_565_);
return v___x_570_;
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_array_get_size(v_args_565_);
v___x_572_ = lean_array_get_size(v_args_568_);
v___x_573_ = lean_nat_dec_eq(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec_ref(v_args_568_);
lean_dec_ref(v_args_565_);
return v___x_573_;
}
else
{
uint8_t v___x_574_; 
v___x_574_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_args_565_, v_args_568_, v___x_571_);
lean_dec_ref(v_args_568_);
lean_dec_ref(v_args_565_);
return v___x_574_;
}
}
}
}
else
{
uint8_t v___x_575_; 
lean_dec_ref_known(v_x_559_, 3);
lean_dec(v_x_560_);
v___x_575_ = 0;
return v___x_575_;
}
}
case 2:
{
if (lean_obj_tag(v_x_560_) == 2)
{
lean_object* v_info_576_; lean_object* v_val_577_; lean_object* v_info_578_; lean_object* v_val_579_; uint8_t v___x_580_; 
v_info_576_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_info_576_);
v_val_577_ = lean_ctor_get(v_x_559_, 1);
lean_inc_ref(v_val_577_);
lean_dec_ref_known(v_x_559_, 2);
v_info_578_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_info_578_);
v_val_579_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_val_579_);
lean_dec_ref_known(v_x_560_, 2);
v___x_580_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_576_, v_info_578_);
if (v___x_580_ == 0)
{
lean_dec_ref(v_val_579_);
lean_dec_ref(v_val_577_);
return v___x_580_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = lean_string_dec_eq(v_val_577_, v_val_579_);
lean_dec_ref(v_val_579_);
lean_dec_ref(v_val_577_);
return v___x_581_;
}
}
else
{
uint8_t v___x_582_; 
lean_dec_ref_known(v_x_559_, 2);
lean_dec(v_x_560_);
v___x_582_ = 0;
return v___x_582_;
}
}
default: 
{
if (lean_obj_tag(v_x_560_) == 3)
{
lean_object* v_info_583_; lean_object* v_rawVal_584_; lean_object* v_val_585_; lean_object* v_preresolved_586_; lean_object* v_info_587_; lean_object* v_rawVal_588_; lean_object* v_val_589_; lean_object* v_preresolved_590_; uint8_t v___x_591_; 
v_info_583_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_info_583_);
v_rawVal_584_ = lean_ctor_get(v_x_559_, 1);
lean_inc_ref(v_rawVal_584_);
v_val_585_ = lean_ctor_get(v_x_559_, 2);
lean_inc(v_val_585_);
v_preresolved_586_ = lean_ctor_get(v_x_559_, 3);
lean_inc(v_preresolved_586_);
lean_dec_ref_known(v_x_559_, 4);
v_info_587_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_info_587_);
v_rawVal_588_ = lean_ctor_get(v_x_560_, 1);
lean_inc_ref(v_rawVal_588_);
v_val_589_ = lean_ctor_get(v_x_560_, 2);
lean_inc(v_val_589_);
v_preresolved_590_ = lean_ctor_get(v_x_560_, 3);
lean_inc(v_preresolved_590_);
lean_dec_ref_known(v_x_560_, 4);
v___x_591_ = l_Lean_instBEqSourceInfo__lean_beq(v_info_583_, v_info_587_);
if (v___x_591_ == 0)
{
lean_dec(v_preresolved_590_);
lean_dec(v_val_589_);
lean_dec_ref(v_rawVal_588_);
lean_dec(v_preresolved_586_);
lean_dec(v_val_585_);
lean_dec_ref(v_rawVal_584_);
return v___x_591_;
}
else
{
uint8_t v___x_592_; 
v___x_592_ = l_Substring_Raw_beq(v_rawVal_584_, v_rawVal_588_);
if (v___x_592_ == 0)
{
lean_dec(v_preresolved_590_);
lean_dec(v_val_589_);
lean_dec(v_preresolved_586_);
lean_dec(v_val_585_);
return v___x_592_;
}
else
{
uint8_t v___x_593_; 
v___x_593_ = lean_name_eq(v_val_585_, v_val_589_);
lean_dec(v_val_589_);
lean_dec(v_val_585_);
if (v___x_593_ == 0)
{
lean_dec(v_preresolved_590_);
lean_dec(v_preresolved_586_);
return v___x_593_;
}
else
{
uint8_t v___x_594_; 
v___x_594_ = l_List_beq___at___00Lean_Syntax_structRangeEq_spec__2(v_preresolved_586_, v_preresolved_590_);
lean_dec(v_preresolved_590_);
lean_dec(v_preresolved_586_);
return v___x_594_;
}
}
}
}
else
{
uint8_t v___x_595_; 
lean_dec_ref_known(v_x_559_, 4);
lean_dec(v_x_560_);
v___x_595_ = 0;
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(lean_object* v_xs_596_, lean_object* v_ys_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_zero_599_; uint8_t v_isZero_600_; 
v_zero_599_ = lean_unsigned_to_nat(0u);
v_isZero_600_ = lean_nat_dec_eq(v_x_598_, v_zero_599_);
if (v_isZero_600_ == 1)
{
lean_dec(v_x_598_);
return v_isZero_600_;
}
else
{
lean_object* v_one_601_; lean_object* v_n_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_one_601_ = lean_unsigned_to_nat(1u);
v_n_602_ = lean_nat_sub(v_x_598_, v_one_601_);
lean_dec(v_x_598_);
v___x_603_ = lean_array_fget_borrowed(v_xs_596_, v_n_602_);
v___x_604_ = lean_array_fget_borrowed(v_ys_597_, v_n_602_);
lean_inc(v___x_604_);
lean_inc(v___x_603_);
v___x_605_ = l_Lean_Syntax_eqWithInfo(v___x_603_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_n_602_);
return v___x_605_;
}
else
{
v_x_598_ = v_n_602_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg___boxed(lean_object* v_xs_607_, lean_object* v_ys_608_, lean_object* v_x_609_){
_start:
{
uint8_t v_res_610_; lean_object* v_r_611_; 
v_res_610_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_607_, v_ys_608_, v_x_609_);
lean_dec_ref(v_ys_608_);
lean_dec_ref(v_xs_607_);
v_r_611_ = lean_box(v_res_610_);
return v_r_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfo___boxed(lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
uint8_t v_res_614_; lean_object* v_r_615_; 
v_res_614_ = l_Lean_Syntax_eqWithInfo(v_x_612_, v_x_613_);
v_r_615_ = lean_box(v_res_614_);
return v_r_615_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(lean_object* v_xs_616_, lean_object* v_ys_617_, lean_object* v_hsz_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___redArg(v_xs_616_, v_ys_617_, v_x_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0___boxed(lean_object* v_xs_622_, lean_object* v_ys_623_, lean_object* v_hsz_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Array_isEqvAux___at___00Lean_Syntax_eqWithInfo_spec__0(v_xs_622_, v_ys_623_, v_hsz_624_, v_x_625_, v_x_626_);
lean_dec_ref(v_ys_623_);
lean_dec_ref(v_xs_622_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_eqWithInfoAndTraceReuse(lean_object* v_opts_629_, lean_object* v_stx1_630_, lean_object* v_stx2_631_){
_start:
{
uint8_t v___x_632_; uint8_t v___x_633_; 
lean_inc(v_stx2_631_);
lean_inc(v_stx1_630_);
v___x_632_ = l_Lean_Syntax_eqWithInfo(v_stx1_630_, v_stx2_631_);
v___x_633_ = 1;
if (v___x_632_ == 0)
{
lean_object* v_map_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_map_634_ = lean_ctor_get(v_opts_629_, 0);
v___x_635_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__3));
v___x_636_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_634_, v___x_635_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_dec(v_stx2_631_);
lean_dec(v_stx1_630_);
return v___x_632_;
}
else
{
lean_object* v_val_637_; 
v_val_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v___x_636_, 1);
if (lean_obj_tag(v_val_637_) == 1)
{
uint8_t v_v_638_; 
v_v_638_ = lean_ctor_get_uint8(v_val_637_, 0);
lean_dec_ref_known(v_val_637_, 0);
if (v_v_638_ == 0)
{
lean_dec(v_stx2_631_);
lean_dec(v_stx1_630_);
return v___x_632_;
}
else
{
lean_object* v___x_639_; lean_object* v___f_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_639_ = lean_box(v___x_632_);
v___f_640_ = lean_alloc_closure((void*)(l_Lean_Syntax_structRangeEqWithTraceReuse___lam__0___boxed), 2, 1);
lean_closure_set(v___f_640_, 0, v___x_639_);
v___x_641_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__4));
v___x_642_ = lean_box(0);
v___x_643_ = l_Lean_Syntax_formatStx(v_stx1_630_, v___x_642_, v___x_633_);
v___x_644_ = l_Std_Format_defWidth;
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_Std_Format_pretty(v___x_643_, v___x_644_, v___x_645_, v___x_645_);
v___x_647_ = lean_string_append(v___x_641_, v___x_646_);
lean_dec_ref(v___x_646_);
v___x_648_ = ((lean_object*)(l_Lean_Syntax_structRangeEqWithTraceReuse___closed__5));
v___x_649_ = lean_string_append(v___x_647_, v___x_648_);
v___x_650_ = l_Lean_Syntax_formatStx(v_stx2_631_, v___x_642_, v___x_633_);
v___x_651_ = l_Std_Format_pretty(v___x_650_, v___x_644_, v___x_645_, v___x_645_);
v___x_652_ = lean_string_append(v___x_649_, v___x_651_);
lean_dec_ref(v___x_651_);
v___x_653_ = lean_dbg_trace(v___x_652_, v___f_640_);
v___x_654_ = lean_unbox(v___x_653_);
lean_dec(v___x_653_);
return v___x_654_;
}
}
else
{
lean_dec(v_val_637_);
lean_dec(v_stx2_631_);
lean_dec(v_stx1_630_);
return v___x_632_;
}
}
}
else
{
lean_dec(v_stx2_631_);
lean_dec(v_stx1_630_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eqWithInfoAndTraceReuse___boxed(lean_object* v_opts_655_, lean_object* v_stx1_656_, lean_object* v_stx2_657_){
_start:
{
uint8_t v_res_658_; lean_object* v_r_659_; 
v_res_658_ = l_Lean_Syntax_eqWithInfoAndTraceReuse(v_opts_655_, v_stx1_656_, v_stx2_657_);
lean_dec_ref(v_opts_655_);
v_r_659_ = lean_box(v_res_658_);
return v_r_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal(lean_object* v_x_661_){
_start:
{
if (lean_obj_tag(v_x_661_) == 2)
{
lean_object* v_val_662_; 
v_val_662_ = lean_ctor_get(v_x_661_, 1);
lean_inc_ref(v_val_662_);
return v_val_662_;
}
else
{
lean_object* v___x_663_; 
v___x_663_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
return v___x_663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAtomVal___boxed(lean_object* v_x_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Syntax_getAtomVal(v_x_664_);
lean_dec(v_x_664_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_setAtomVal(lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
if (lean_obj_tag(v_x_666_) == 2)
{
lean_object* v_info_668_; lean_object* v___x_670_; uint8_t v_isShared_671_; uint8_t v_isSharedCheck_675_; 
v_info_668_ = lean_ctor_get(v_x_666_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v_x_666_);
if (v_isSharedCheck_675_ == 0)
{
lean_object* v_unused_676_; 
v_unused_676_ = lean_ctor_get(v_x_666_, 1);
lean_dec(v_unused_676_);
v___x_670_ = v_x_666_;
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
else
{
lean_inc(v_info_668_);
lean_dec(v_x_666_);
v___x_670_ = lean_box(0);
v_isShared_671_ = v_isSharedCheck_675_;
goto v_resetjp_669_;
}
v_resetjp_669_:
{
lean_object* v___x_673_; 
if (v_isShared_671_ == 0)
{
lean_ctor_set(v___x_670_, 1, v_x_667_);
v___x_673_ = v___x_670_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_info_668_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_x_667_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_dec_ref(v_x_667_);
return v_x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode___redArg(lean_object* v_stx_677_, lean_object* v_hyes_678_, lean_object* v_hno_679_){
_start:
{
if (lean_obj_tag(v_stx_677_) == 1)
{
lean_object* v___x_680_; 
lean_dec(v_hno_679_);
v___x_680_ = lean_apply_1(v_hyes_678_, v_stx_677_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v_hyes_678_);
lean_dec(v_stx_677_);
v___x_681_ = lean_box(0);
v___x_682_ = lean_apply_1(v_hno_679_, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNode(lean_object* v_00_u03b2_683_, lean_object* v_stx_684_, lean_object* v_hyes_685_, lean_object* v_hno_686_){
_start:
{
if (lean_obj_tag(v_stx_684_) == 1)
{
lean_object* v___x_687_; 
lean_dec(v_hno_686_);
v___x_687_ = lean_apply_1(v_hyes_685_, v_stx_684_);
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_hyes_685_);
lean_dec(v_stx_684_);
v___x_688_ = lean_box(0);
v___x_689_ = lean_apply_1(v_hno_686_, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg(lean_object* v_stx_690_, lean_object* v_kind_691_, lean_object* v_hyes_692_, lean_object* v_hno_693_){
_start:
{
if (lean_obj_tag(v_stx_690_) == 1)
{
lean_object* v_kind_694_; uint8_t v___x_695_; 
v_kind_694_ = lean_ctor_get(v_stx_690_, 1);
v___x_695_ = lean_name_eq(v_kind_694_, v_kind_691_);
if (v___x_695_ == 0)
{
lean_object* v___x_696_; lean_object* v___x_697_; 
lean_dec_ref_known(v_stx_690_, 3);
lean_dec(v_hyes_692_);
v___x_696_ = lean_box(0);
v___x_697_ = lean_apply_1(v_hno_693_, v___x_696_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; 
lean_dec(v_hno_693_);
v___x_698_ = lean_apply_1(v_hyes_692_, v_stx_690_);
return v___x_698_;
}
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v_hyes_692_);
lean_dec(v_stx_690_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_apply_1(v_hno_693_, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___redArg___boxed(lean_object* v_stx_701_, lean_object* v_kind_702_, lean_object* v_hyes_703_, lean_object* v_hno_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Lean_Syntax_ifNodeKind___redArg(v_stx_701_, v_kind_702_, v_hyes_703_, v_hno_704_);
lean_dec(v_kind_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind(lean_object* v_00_u03b2_706_, lean_object* v_stx_707_, lean_object* v_kind_708_, lean_object* v_hyes_709_, lean_object* v_hno_710_){
_start:
{
if (lean_obj_tag(v_stx_707_) == 1)
{
lean_object* v_kind_711_; uint8_t v___x_712_; 
v_kind_711_ = lean_ctor_get(v_stx_707_, 1);
v___x_712_ = lean_name_eq(v_kind_711_, v_kind_708_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref_known(v_stx_707_, 3);
lean_dec(v_hyes_709_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_apply_1(v_hno_710_, v___x_713_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; 
lean_dec(v_hno_710_);
v___x_715_ = lean_apply_1(v_hyes_709_, v_stx_707_);
return v___x_715_;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_hyes_709_);
lean_dec(v_stx_707_);
v___x_716_ = lean_box(0);
v___x_717_ = lean_apply_1(v_hno_710_, v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ifNodeKind___boxed(lean_object* v_00_u03b2_718_, lean_object* v_stx_719_, lean_object* v_kind_720_, lean_object* v_hyes_721_, lean_object* v_hno_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Syntax_ifNodeKind(v_00_u03b2_718_, v_stx_719_, v_kind_720_, v_hyes_721_, v_hno_722_);
lean_dec(v_kind_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode(lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 1)
{
lean_inc_ref(v_x_733_);
return v_x_733_;
}
else
{
lean_object* v___x_734_; 
v___x_734_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_asNode___boxed(lean_object* v_x_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Syntax_asNode(v_x_735_);
lean_dec(v_x_735_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt(lean_object* v_stx_737_, lean_object* v_i_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = l_Lean_Syntax_getArg(v_stx_737_, v_i_738_);
v___x_740_ = l_Lean_Syntax_getId(v___x_739_);
lean_dec(v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getIdAt___boxed(lean_object* v_stx_741_, lean_object* v_i_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Syntax_getIdAt(v_stx_741_, v_i_742_);
lean_dec(v_i_742_);
lean_dec(v_stx_741_);
return v_res_743_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasIdent(lean_object* v_id_744_, lean_object* v_x_745_){
_start:
{
switch(lean_obj_tag(v_x_745_))
{
case 3:
{
lean_object* v_val_746_; uint8_t v___x_747_; 
v_val_746_ = lean_ctor_get(v_x_745_, 2);
v___x_747_ = lean_name_eq(v_id_744_, v_val_746_);
return v___x_747_;
}
case 1:
{
lean_object* v_args_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_args_748_ = lean_ctor_get(v_x_745_, 2);
v___x_749_ = lean_unsigned_to_nat(0u);
v___x_750_ = lean_array_get_size(v_args_748_);
v___x_751_ = lean_nat_dec_lt(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
return v___x_751_;
}
else
{
if (v___x_751_ == 0)
{
return v___x_751_;
}
else
{
size_t v___x_752_; size_t v___x_753_; uint8_t v___x_754_; 
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_750_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_744_, v_args_748_, v___x_752_, v___x_753_);
return v___x_754_;
}
}
}
default: 
{
uint8_t v___x_755_; 
v___x_755_ = 0;
return v___x_755_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(lean_object* v_id_756_, lean_object* v_as_757_, size_t v_i_758_, size_t v_stop_759_){
_start:
{
uint8_t v___x_760_; 
v___x_760_ = lean_usize_dec_eq(v_i_758_, v_stop_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_array_uget_borrowed(v_as_757_, v_i_758_);
v___x_762_ = l_Lean_Syntax_hasIdent(v_id_756_, v___x_761_);
if (v___x_762_ == 0)
{
size_t v___x_763_; size_t v___x_764_; 
v___x_763_ = ((size_t)1ULL);
v___x_764_ = lean_usize_add(v_i_758_, v___x_763_);
v_i_758_ = v___x_764_;
goto _start;
}
else
{
return v___x_762_;
}
}
else
{
uint8_t v___x_766_; 
v___x_766_ = 0;
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0___boxed(lean_object* v_id_767_, lean_object* v_as_768_, lean_object* v_i_769_, lean_object* v_stop_770_){
_start:
{
size_t v_i_boxed_771_; size_t v_stop_boxed_772_; uint8_t v_res_773_; lean_object* v_r_774_; 
v_i_boxed_771_ = lean_unbox_usize(v_i_769_);
lean_dec(v_i_769_);
v_stop_boxed_772_ = lean_unbox_usize(v_stop_770_);
lean_dec(v_stop_770_);
v_res_773_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_hasIdent_spec__0(v_id_767_, v_as_768_, v_i_boxed_771_, v_stop_boxed_772_);
lean_dec_ref(v_as_768_);
lean_dec(v_id_767_);
v_r_774_ = lean_box(v_res_773_);
return v_r_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasIdent___boxed(lean_object* v_id_775_, lean_object* v_x_776_){
_start:
{
uint8_t v_res_777_; lean_object* v_r_778_; 
v_res_777_ = l_Lean_Syntax_hasIdent(v_id_775_, v_x_776_);
lean_dec(v_x_776_);
lean_dec(v_id_775_);
v_r_778_ = lean_box(v_res_777_);
return v_r_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArgs(lean_object* v_stx_779_, lean_object* v_fn_780_){
_start:
{
if (lean_obj_tag(v_stx_779_) == 1)
{
lean_object* v_info_781_; lean_object* v_kind_782_; lean_object* v_args_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_791_; 
v_info_781_ = lean_ctor_get(v_stx_779_, 0);
v_kind_782_ = lean_ctor_get(v_stx_779_, 1);
v_args_783_ = lean_ctor_get(v_stx_779_, 2);
v_isSharedCheck_791_ = !lean_is_exclusive(v_stx_779_);
if (v_isSharedCheck_791_ == 0)
{
v___x_785_ = v_stx_779_;
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_args_783_);
lean_inc(v_kind_782_);
lean_inc(v_info_781_);
lean_dec(v_stx_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_791_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
v___x_787_ = lean_apply_1(v_fn_780_, v_args_783_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 2, v___x_787_);
v___x_789_ = v___x_785_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_info_781_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_kind_782_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_dec_ref(v_fn_780_);
return v_stx_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg(lean_object* v_stx_792_, lean_object* v_i_793_, lean_object* v_fn_794_){
_start:
{
if (lean_obj_tag(v_stx_792_) == 1)
{
lean_object* v_info_795_; lean_object* v_kind_796_; lean_object* v_args_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_info_795_ = lean_ctor_get(v_stx_792_, 0);
v_kind_796_ = lean_ctor_get(v_stx_792_, 1);
v_args_797_ = lean_ctor_get(v_stx_792_, 2);
v___x_798_ = lean_array_get_size(v_args_797_);
v___x_799_ = lean_nat_dec_lt(v_i_793_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_fn_794_);
return v_stx_792_;
}
else
{
lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_811_; 
lean_inc_ref(v_args_797_);
lean_inc(v_kind_796_);
lean_inc(v_info_795_);
v_isSharedCheck_811_ = !lean_is_exclusive(v_stx_792_);
if (v_isSharedCheck_811_ == 0)
{
lean_object* v_unused_812_; lean_object* v_unused_813_; lean_object* v_unused_814_; 
v_unused_812_ = lean_ctor_get(v_stx_792_, 2);
lean_dec(v_unused_812_);
v_unused_813_ = lean_ctor_get(v_stx_792_, 1);
lean_dec(v_unused_813_);
v_unused_814_ = lean_ctor_get(v_stx_792_, 0);
lean_dec(v_unused_814_);
v___x_801_ = v_stx_792_;
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
else
{
lean_dec(v_stx_792_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_811_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_v_803_; lean_object* v___x_804_; lean_object* v_xs_x27_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v_v_803_ = lean_array_fget(v_args_797_, v_i_793_);
v___x_804_ = lean_box(0);
v_xs_x27_805_ = lean_array_fset(v_args_797_, v_i_793_, v___x_804_);
v___x_806_ = lean_apply_1(v_fn_794_, v_v_803_);
v___x_807_ = lean_array_fset(v_xs_x27_805_, v_i_793_, v___x_806_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 2, v___x_807_);
v___x_809_ = v___x_801_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_info_795_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_kind_796_);
lean_ctor_set(v_reuseFailAlloc_810_, 2, v___x_807_);
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
else
{
lean_dec_ref(v_fn_794_);
return v_stx_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_modifyArg___boxed(lean_object* v_stx_815_, lean_object* v_i_816_, lean_object* v_fn_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Syntax_modifyArg(v_stx_815_, v_i_816_, v_fn_817_);
lean_dec(v_i_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__0(lean_object* v_info_819_, lean_object* v_kind_820_, lean_object* v_toPure_821_, lean_object* v_____do__lift_822_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_823_, 0, v_info_819_);
lean_ctor_set(v___x_823_, 1, v_kind_820_);
lean_ctor_set(v___x_823_, 2, v_____do__lift_822_);
v___x_824_ = lean_apply_2(v_toPure_821_, lean_box(0), v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__2(lean_object* v_toPure_825_, lean_object* v_x_826_, lean_object* v_o_827_){
_start:
{
if (lean_obj_tag(v_o_827_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_apply_2(v_toPure_825_, lean_box(0), v_x_826_);
return v___x_828_;
}
else
{
lean_object* v_val_829_; lean_object* v___x_830_; 
lean_dec(v_x_826_);
v_val_829_ = lean_ctor_get(v_o_827_, 0);
lean_inc(v_val_829_);
lean_dec_ref_known(v_o_827_, 1);
v___x_830_ = lean_apply_2(v_toPure_825_, lean_box(0), v_val_829_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg(lean_object* v_inst_831_, lean_object* v_fn_832_, lean_object* v_x_833_){
_start:
{
if (lean_obj_tag(v_x_833_) == 1)
{
lean_object* v_toApplicative_834_; lean_object* v_toBind_835_; lean_object* v_toPure_836_; lean_object* v_info_837_; lean_object* v_kind_838_; lean_object* v_args_839_; lean_object* v___f_840_; lean_object* v___f_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_toApplicative_834_ = lean_ctor_get(v_inst_831_, 0);
v_toBind_835_ = lean_ctor_get(v_inst_831_, 1);
lean_inc_n(v_toBind_835_, 2);
v_toPure_836_ = lean_ctor_get(v_toApplicative_834_, 1);
lean_inc_n(v_toPure_836_, 2);
v_info_837_ = lean_ctor_get(v_x_833_, 0);
v_kind_838_ = lean_ctor_get(v_x_833_, 1);
v_args_839_ = lean_ctor_get(v_x_833_, 2);
lean_inc(v_kind_838_);
lean_inc(v_info_837_);
v___f_840_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_840_, 0, v_info_837_);
lean_closure_set(v___f_840_, 1, v_kind_838_);
lean_closure_set(v___f_840_, 2, v_toPure_836_);
lean_inc_ref(v_args_839_);
lean_inc(v_fn_832_);
v___f_841_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__1), 7, 6);
lean_closure_set(v___f_841_, 0, v_inst_831_);
lean_closure_set(v___f_841_, 1, v_fn_832_);
lean_closure_set(v___f_841_, 2, v_args_839_);
lean_closure_set(v___f_841_, 3, v_toBind_835_);
lean_closure_set(v___f_841_, 4, v___f_840_);
lean_closure_set(v___f_841_, 5, v_toPure_836_);
v___x_842_ = lean_apply_1(v_fn_832_, v_x_833_);
v___x_843_ = lean_apply_4(v_toBind_835_, lean_box(0), lean_box(0), v___x_842_, v___f_841_);
return v___x_843_;
}
else
{
lean_object* v_toApplicative_844_; lean_object* v_toBind_845_; lean_object* v_toPure_846_; lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_toApplicative_844_ = lean_ctor_get(v_inst_831_, 0);
lean_inc_ref(v_toApplicative_844_);
v_toBind_845_ = lean_ctor_get(v_inst_831_, 1);
lean_inc(v_toBind_845_);
lean_dec_ref(v_inst_831_);
v_toPure_846_ = lean_ctor_get(v_toApplicative_844_, 1);
lean_inc(v_toPure_846_);
lean_dec_ref(v_toApplicative_844_);
lean_inc(v_x_833_);
v___f_847_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg___lam__2), 3, 2);
lean_closure_set(v___f_847_, 0, v_toPure_846_);
lean_closure_set(v___f_847_, 1, v_x_833_);
v___x_848_ = lean_apply_1(v_fn_832_, v_x_833_);
v___x_849_ = lean_apply_4(v_toBind_845_, lean_box(0), lean_box(0), v___x_848_, v___f_847_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___redArg___lam__1(lean_object* v_inst_850_, lean_object* v_fn_851_, lean_object* v_args_852_, lean_object* v_toBind_853_, lean_object* v___f_854_, lean_object* v_toPure_855_, lean_object* v_____do__lift_856_){
_start:
{
if (lean_obj_tag(v_____do__lift_856_) == 0)
{
lean_object* v___x_857_; size_t v_sz_858_; size_t v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v_toPure_855_);
lean_inc_ref(v_inst_850_);
v___x_857_ = lean_alloc_closure((void*)(l_Lean_Syntax_replaceM___redArg), 3, 2);
lean_closure_set(v___x_857_, 0, v_inst_850_);
lean_closure_set(v___x_857_, 1, v_fn_851_);
v_sz_858_ = lean_array_size(v_args_852_);
v___x_859_ = ((size_t)0ULL);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_850_, v___x_857_, v_sz_858_, v___x_859_, v_args_852_);
v___x_861_ = lean_apply_4(v_toBind_853_, lean_box(0), lean_box(0), v___x_860_, v___f_854_);
return v___x_861_;
}
else
{
lean_object* v_val_862_; lean_object* v___x_863_; 
lean_dec(v___f_854_);
lean_dec(v_toBind_853_);
lean_dec_ref(v_args_852_);
lean_dec(v_fn_851_);
lean_dec_ref(v_inst_850_);
v_val_862_ = lean_ctor_get(v_____do__lift_856_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_____do__lift_856_, 1);
v___x_863_ = lean_apply_2(v_toPure_855_, lean_box(0), v_val_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM(lean_object* v_m_864_, lean_object* v_inst_865_, lean_object* v_fn_866_, lean_object* v_x_867_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Syntax_replaceM___redArg(v_inst_865_, v_fn_866_, v_x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0(lean_object* v_info_869_, lean_object* v_kind_870_, lean_object* v_fn_871_, lean_object* v_args_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_873_, 0, v_info_869_);
lean_ctor_set(v___x_873_, 1, v_kind_870_);
lean_ctor_set(v___x_873_, 2, v_args_872_);
v___x_874_ = lean_apply_1(v_fn_871_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___redArg(lean_object* v_inst_875_, lean_object* v_fn_876_, lean_object* v_x_877_){
_start:
{
if (lean_obj_tag(v_x_877_) == 1)
{
lean_object* v_toBind_878_; lean_object* v_info_879_; lean_object* v_kind_880_; lean_object* v_args_881_; lean_object* v___f_882_; lean_object* v___x_883_; size_t v_sz_884_; size_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_toBind_878_ = lean_ctor_get(v_inst_875_, 1);
lean_inc(v_toBind_878_);
v_info_879_ = lean_ctor_get(v_x_877_, 0);
lean_inc(v_info_879_);
v_kind_880_ = lean_ctor_get(v_x_877_, 1);
lean_inc(v_kind_880_);
v_args_881_ = lean_ctor_get(v_x_877_, 2);
lean_inc_ref(v_args_881_);
lean_dec_ref_known(v_x_877_, 3);
lean_inc(v_fn_876_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_882_, 0, v_info_879_);
lean_closure_set(v___f_882_, 1, v_kind_880_);
lean_closure_set(v___f_882_, 2, v_fn_876_);
lean_inc_ref(v_inst_875_);
v___x_883_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUpM___redArg), 3, 2);
lean_closure_set(v___x_883_, 0, v_inst_875_);
lean_closure_set(v___x_883_, 1, v_fn_876_);
v_sz_884_ = lean_array_size(v_args_881_);
v___x_885_ = ((size_t)0ULL);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_875_, v___x_883_, v_sz_884_, v___x_885_, v_args_881_);
v___x_887_ = lean_apply_4(v_toBind_878_, lean_box(0), lean_box(0), v___x_886_, v___f_882_);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
lean_dec_ref(v_inst_875_);
v___x_888_ = lean_apply_1(v_fn_876_, v_x_877_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM(lean_object* v_m_889_, lean_object* v_inst_890_, lean_object* v_fn_891_, lean_object* v_x_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v_inst_890_, v_fn_891_, v_x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp___lam__0(lean_object* v_fn_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_apply_1(v_fn_894_, v_x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUp(lean_object* v_fn_916_, lean_object* v_stx_917_){
_start:
{
lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Syntax_rewriteBottomUp___lam__0), 2, 1);
lean_closure_set(v___f_918_, 0, v_fn_916_);
v___x_919_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUp___closed__9));
v___x_920_ = l_Lean_Syntax_rewriteBottomUpM___redArg(v___x_919_, v___f_918_, v_stx_917_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__0(lean_object* v_msg_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = l_String_instInhabitedSlice;
v___x_923_ = lean_panic_fn_borrowed(v___x_922_, v_msg_921_);
return v___x_923_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___redArg(lean_object* v_s_924_, lean_object* v_a_925_, uint8_t v_b_926_){
_start:
{
lean_object* v_str_927_; lean_object* v_startInclusive_928_; lean_object* v_endExclusive_929_; lean_object* v___x_930_; uint8_t v_decide_931_; 
v_str_927_ = lean_ctor_get(v_s_924_, 0);
v_startInclusive_928_ = lean_ctor_get(v_s_924_, 1);
v_endExclusive_929_ = lean_ctor_get(v_s_924_, 2);
v___x_930_ = lean_nat_sub(v_endExclusive_929_, v_startInclusive_928_);
v_decide_931_ = lean_nat_dec_eq(v_a_925_, v___x_930_);
lean_dec(v___x_930_);
if (v_decide_931_ == 0)
{
uint32_t v___x_932_; lean_object* v___x_933_; uint32_t v___x_934_; uint8_t v___x_935_; 
v___x_932_ = 64;
v___x_933_ = lean_nat_add(v_startInclusive_928_, v_a_925_);
lean_dec(v_a_925_);
v___x_934_ = lean_string_utf8_get_fast(v_str_927_, v___x_933_);
v___x_935_ = lean_uint32_dec_eq(v___x_934_, v___x_932_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = lean_string_utf8_next_fast(v_str_927_, v___x_933_);
lean_dec(v___x_933_);
v___x_937_ = lean_nat_sub(v___x_936_, v_startInclusive_928_);
v_a_925_ = v___x_937_;
v_b_926_ = v___x_935_;
goto _start;
}
else
{
lean_dec(v___x_933_);
return v___x_935_;
}
}
else
{
lean_dec(v_a_925_);
return v_b_926_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___redArg___boxed(lean_object* v_s_939_, lean_object* v_a_940_, lean_object* v_b_941_){
_start:
{
uint8_t v_b_boxed_942_; uint8_t v_res_943_; lean_object* v_r_944_; 
v_b_boxed_942_ = lean_unbox(v_b_941_);
v_res_943_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___redArg(v_s_939_, v_a_940_, v_b_boxed_942_);
lean_dec_ref(v_s_939_);
v_r_944_ = lean_box(v_res_943_);
return v_r_944_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1(lean_object* v_s_945_){
_start:
{
lean_object* v_searcher_946_; uint8_t v___x_947_; uint8_t v___x_948_; 
v_searcher_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = 0;
v___x_948_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___redArg(v_s_945_, v_searcher_946_, v___x_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1___boxed(lean_object* v_s_949_){
_start:
{
uint8_t v_res_950_; lean_object* v_r_951_; 
v_res_950_ = l_String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1(v_s_949_);
lean_dec_ref(v_s_949_);
v_r_951_ = lean_box(v_res_950_);
return v_r_951_;
}
}
static lean_object* _init_l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__3(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_955_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__2));
v___x_956_ = lean_unsigned_to_nat(14u);
v___x_957_ = lean_unsigned_to_nat(22u);
v___x_958_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__1));
v___x_959_ = ((lean_object*)(l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__0));
v___x_960_ = l_mkPanicMessageWithDecl(v___x_959_, v___x_958_, v___x_957_, v___x_956_, v___x_955_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2(lean_object* v_x_961_){
_start:
{
if (lean_obj_tag(v_x_961_) == 1)
{
lean_object* v_info_962_; lean_object* v_kind_963_; lean_object* v_args_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_974_; 
v_info_962_ = lean_ctor_get(v_x_961_, 0);
v_kind_963_ = lean_ctor_get(v_x_961_, 1);
v_args_964_ = lean_ctor_get(v_x_961_, 2);
v_isSharedCheck_974_ = !lean_is_exclusive(v_x_961_);
if (v_isSharedCheck_974_ == 0)
{
v___x_966_ = v_x_961_;
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_args_964_);
lean_inc(v_kind_963_);
lean_inc(v_info_962_);
lean_dec(v_x_961_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_974_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
size_t v_sz_968_; size_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_972_; 
v_sz_968_ = lean_array_size(v_args_964_);
v___x_969_ = ((size_t)0ULL);
v___x_970_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2_spec__3(v_sz_968_, v___x_969_, v_args_964_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 2, v___x_970_);
v___x_972_ = v___x_966_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_info_962_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v_kind_963_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v___x_970_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
if (lean_obj_tag(v_x_961_) == 3)
{
lean_object* v_info_975_; lean_object* v_rawVal_976_; lean_object* v_val_977_; lean_object* v_preresolved_978_; uint8_t v___y_980_; lean_object* v_str_987_; lean_object* v_startPos_988_; lean_object* v_stopPos_989_; uint8_t v___x_990_; 
v_info_975_ = lean_ctor_get(v_x_961_, 0);
v_rawVal_976_ = lean_ctor_get(v_x_961_, 1);
v_val_977_ = lean_ctor_get(v_x_961_, 2);
v_preresolved_978_ = lean_ctor_get(v_x_961_, 3);
v_str_987_ = lean_ctor_get(v_rawVal_976_, 0);
v_startPos_988_ = lean_ctor_get(v_rawVal_976_, 1);
v_stopPos_989_ = lean_ctor_get(v_rawVal_976_, 2);
v___x_990_ = lean_string_is_valid_pos(v_str_987_, v_startPos_988_);
if (v___x_990_ == 0)
{
goto v___jp_983_;
}
else
{
uint8_t v___x_991_; 
v___x_991_ = lean_string_is_valid_pos(v_str_987_, v_stopPos_989_);
if (v___x_991_ == 0)
{
goto v___jp_983_;
}
else
{
uint8_t v___x_992_; 
v___x_992_ = lean_nat_dec_le(v_startPos_988_, v_stopPos_989_);
if (v___x_992_ == 0)
{
goto v___jp_983_;
}
else
{
lean_object* v___x_993_; uint8_t v___x_994_; 
lean_inc(v_stopPos_989_);
lean_inc(v_startPos_988_);
lean_inc_ref(v_str_987_);
v___x_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_993_, 0, v_str_987_);
lean_ctor_set(v___x_993_, 1, v_startPos_988_);
lean_ctor_set(v___x_993_, 2, v_stopPos_989_);
v___x_994_ = l_String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1(v___x_993_);
lean_dec_ref_known(v___x_993_, 3);
v___y_980_ = v___x_994_;
goto v___jp_979_;
}
}
}
v___jp_979_:
{
if (v___y_980_ == 0)
{
lean_object* v___x_981_; lean_object* v___x_982_; 
lean_inc(v_preresolved_978_);
lean_inc(v_val_977_);
lean_inc_ref(v_rawVal_976_);
lean_inc(v_info_975_);
lean_dec_ref_known(v_x_961_, 4);
v___x_981_ = l_Lean_Name_eraseMacroScopes(v_val_977_);
lean_dec(v_val_977_);
v___x_982_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_982_, 0, v_info_975_);
lean_ctor_set(v___x_982_, 1, v_rawVal_976_);
lean_ctor_set(v___x_982_, 2, v___x_981_);
lean_ctor_set(v___x_982_, 3, v_preresolved_978_);
return v___x_982_;
}
else
{
return v_x_961_;
}
}
v___jp_983_:
{
lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v___x_984_ = lean_obj_once(&l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__3, &l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__3_once, _init_l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2___closed__3);
v___x_985_ = l_panic___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__0(v___x_984_);
v___x_986_ = l_String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1(v___x_985_);
lean_dec_ref(v___x_985_);
v___y_980_ = v___x_986_;
goto v___jp_979_;
}
}
else
{
return v_x_961_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2_spec__3(size_t v_sz_995_, size_t v_i_996_, lean_object* v_bs_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = lean_usize_dec_lt(v_i_996_, v_sz_995_);
if (v___x_998_ == 0)
{
return v_bs_997_;
}
else
{
lean_object* v_v_999_; lean_object* v___x_1000_; lean_object* v_bs_x27_1001_; lean_object* v___x_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v_v_999_ = lean_array_uget(v_bs_997_, v_i_996_);
v___x_1000_ = lean_unsigned_to_nat(0u);
v_bs_x27_1001_ = lean_array_uset(v_bs_997_, v_i_996_, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2(v_v_999_);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_996_, v___x_1003_);
v___x_1005_ = lean_array_uset(v_bs_x27_1001_, v_i_996_, v___x_1002_);
v_i_996_ = v___x_1004_;
v_bs_997_ = v___x_1005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2_spec__3___boxed(lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_bs_1009_){
_start:
{
size_t v_sz_boxed_1010_; size_t v_i_boxed_1011_; lean_object* v_res_1012_; 
v_sz_boxed_1010_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1011_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2_spec__3(v_sz_boxed_1010_, v_i_boxed_1011_, v_bs_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_eraseQuoteMacroScopes(lean_object* v_stx_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Syntax_rewriteBottomUpM___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__2(v_stx_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1(lean_object* v_s_1015_, lean_object* v_inst_1016_, lean_object* v_R_1017_, lean_object* v_a_1018_, uint8_t v_b_1019_, lean_object* v_c_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___redArg(v_s_1015_, v_a_1018_, v_b_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1___boxed(lean_object* v_s_1022_, lean_object* v_inst_1023_, lean_object* v_R_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_, lean_object* v_c_1027_){
_start:
{
uint8_t v_b_boxed_1028_; uint8_t v_res_1029_; lean_object* v_r_1030_; 
v_b_boxed_1028_ = lean_unbox(v_b_1026_);
v_res_1029_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Syntax_eraseQuoteMacroScopes_spec__1_spec__1(v_s_1022_, v_inst_1023_, v_R_1024_, v_a_1025_, v_b_boxed_1028_, v_c_1027_);
lean_dec_ref(v_s_1022_);
v_r_1030_ = lean_box(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(lean_object* v_x_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
if (lean_obj_tag(v_x_1031_) == 0)
{
lean_object* v_leading_1034_; lean_object* v_trailing_1035_; lean_object* v_pos_1036_; lean_object* v_endPos_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1064_; 
v_leading_1034_ = lean_ctor_get(v_x_1031_, 0);
v_trailing_1035_ = lean_ctor_get(v_x_1031_, 2);
v_pos_1036_ = lean_ctor_get(v_x_1031_, 1);
v_endPos_1037_ = lean_ctor_get(v_x_1031_, 3);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1039_ = v_x_1031_;
v_isShared_1040_ = v_isSharedCheck_1064_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_endPos_1037_);
lean_inc(v_trailing_1035_);
lean_inc(v_pos_1036_);
lean_inc(v_leading_1034_);
lean_dec(v_x_1031_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1064_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_str_1041_; lean_object* v_stopPos_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1062_; 
v_str_1041_ = lean_ctor_get(v_leading_1034_, 0);
v_stopPos_1042_ = lean_ctor_get(v_leading_1034_, 2);
v_isSharedCheck_1062_ = !lean_is_exclusive(v_leading_1034_);
if (v_isSharedCheck_1062_ == 0)
{
lean_object* v_unused_1063_; 
v_unused_1063_ = lean_ctor_get(v_leading_1034_, 1);
lean_dec(v_unused_1063_);
v___x_1044_ = v_leading_1034_;
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_stopPos_1042_);
lean_inc(v_str_1041_);
lean_dec(v_leading_1034_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1062_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_str_1046_; lean_object* v_startPos_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1060_; 
v_str_1046_ = lean_ctor_get(v_trailing_1035_, 0);
v_startPos_1047_ = lean_ctor_get(v_trailing_1035_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_trailing_1035_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v_trailing_1035_, 2);
lean_dec(v_unused_1061_);
v___x_1049_ = v_trailing_1035_;
v_isShared_1050_ = v_isSharedCheck_1060_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_startPos_1047_);
lean_inc(v_str_1046_);
lean_dec(v_trailing_1035_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1060_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 2, v_stopPos_1042_);
lean_ctor_set(v___x_1049_, 1, v_x_1032_);
lean_ctor_set(v___x_1049_, 0, v_str_1041_);
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_str_1041_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_x_1032_);
lean_ctor_set(v_reuseFailAlloc_1059_, 2, v_stopPos_1042_);
v___x_1052_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 2, v_x_1033_);
lean_ctor_set(v___x_1044_, 1, v_startPos_1047_);
lean_ctor_set(v___x_1044_, 0, v_str_1046_);
v___x_1054_ = v___x_1044_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_str_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_startPos_1047_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_x_1033_);
v___x_1054_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1056_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 2, v___x_1054_);
lean_ctor_set(v___x_1039_, 0, v___x_1052_);
v___x_1056_ = v___x_1039_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_pos_1036_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_endPos_1037_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
}
}
else
{
lean_dec(v_x_1033_);
lean_dec(v_x_1032_);
return v_x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(lean_object* v___x_1065_, lean_object* v___x_1066_, lean_object* v___x_1067_, lean_object* v_a_1068_, lean_object* v_b_1069_){
_start:
{
lean_object* v___x_1070_; uint8_t v_decide_1071_; 
v___x_1070_ = lean_nat_sub(v___x_1065_, v___x_1066_);
v_decide_1071_ = lean_nat_dec_eq(v_a_1068_, v___x_1070_);
lean_dec(v___x_1070_);
if (v_decide_1071_ == 0)
{
uint32_t v___x_1072_; lean_object* v___x_1073_; uint32_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1072_ = 10;
v___x_1073_ = lean_nat_add(v___x_1066_, v_a_1068_);
v___x_1074_ = lean_string_utf8_get_fast(v___x_1067_, v___x_1073_);
v___x_1075_ = lean_uint32_dec_eq(v___x_1074_, v___x_1072_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v_a_1068_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_string_utf8_next_fast(v___x_1067_, v___x_1073_);
lean_dec(v___x_1073_);
v___x_1078_ = lean_nat_sub(v___x_1077_, v___x_1066_);
v_a_1068_ = v___x_1078_;
v_b_1069_ = v___x_1076_;
goto _start;
}
else
{
lean_object* v___x_1080_; 
lean_dec(v___x_1073_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_a_1068_);
return v___x_1080_;
}
}
else
{
lean_dec(v_a_1068_);
lean_inc(v_b_1069_);
return v_b_1069_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg___boxed(lean_object* v___x_1081_, lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1081_, v___x_1082_, v___x_1083_, v_a_1084_, v_b_1085_);
lean_dec(v_b_1085_);
lean_dec_ref(v___x_1083_);
lean_dec(v___x_1082_);
lean_dec(v___x_1081_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(lean_object* v_trail_1087_){
_start:
{
lean_object* v_str_1088_; lean_object* v_startPos_1089_; lean_object* v_stopPos_1090_; uint8_t v___x_1094_; 
v_str_1088_ = lean_ctor_get(v_trail_1087_, 0);
v_startPos_1089_ = lean_ctor_get(v_trail_1087_, 1);
v_stopPos_1090_ = lean_ctor_get(v_trail_1087_, 2);
v___x_1094_ = lean_string_is_valid_pos(v_str_1088_, v_startPos_1089_);
if (v___x_1094_ == 0)
{
goto v___jp_1091_;
}
else
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_string_is_valid_pos(v_str_1088_, v_stopPos_1090_);
if (v___x_1095_ == 0)
{
goto v___jp_1091_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_nat_dec_le(v_startPos_1089_, v_stopPos_1090_);
if (v___x_1096_ == 0)
{
goto v___jp_1091_;
}
else
{
lean_object* v_searcher_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_searcher_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v_stopPos_1090_, v_startPos_1089_, v_str_1088_, v_searcher_1097_, v___x_1098_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_nat_sub(v_stopPos_1090_, v_startPos_1089_);
v___x_1101_ = lean_nat_add(v_startPos_1089_, v___x_1100_);
lean_dec(v___x_1100_);
return v___x_1101_;
}
else
{
lean_object* v_val_1102_; lean_object* v___x_1103_; 
v_val_1102_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1103_ = lean_nat_add(v_startPos_1089_, v_val_1102_);
lean_dec(v_val_1102_);
return v___x_1103_;
}
}
}
}
v___jp_1091_:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_nat_sub(v_stopPos_1090_, v_startPos_1089_);
v___x_1093_ = lean_nat_add(v_startPos_1089_, v___x_1092_);
lean_dec(v___x_1092_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop___boxed(lean_object* v_trail_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trail_1104_);
lean_dec_ref(v_trail_1104_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(lean_object* v___x_1106_, lean_object* v___x_1107_, lean_object* v___x_1108_, lean_object* v___x_1109_, lean_object* v_inst_1110_, lean_object* v_R_1111_, lean_object* v_a_1112_, lean_object* v_b_1113_, lean_object* v_c_1114_){
_start:
{
lean_object* v___x_1115_; 
v___x_1115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___redArg(v___x_1106_, v___x_1107_, v___x_1109_, v_a_1112_, v_b_1113_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0___boxed(lean_object* v___x_1116_, lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v_inst_1120_, lean_object* v_R_1121_, lean_object* v_a_1122_, lean_object* v_b_1123_, lean_object* v_c_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop_spec__0(v___x_1116_, v___x_1117_, v___x_1118_, v___x_1119_, v_inst_1120_, v_R_1121_, v_a_1122_, v_b_1123_, v_c_1124_);
lean_dec(v_b_1123_);
lean_dec_ref(v___x_1119_);
lean_dec_ref(v___x_1118_);
lean_dec(v___x_1117_);
lean_dec(v___x_1116_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_updateLeadingAux(lean_object* v_x_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___y_1129_; 
switch(lean_obj_tag(v_x_1126_))
{
case 2:
{
lean_object* v_info_1132_; 
v_info_1132_ = lean_ctor_get(v_x_1126_, 0);
lean_inc(v_info_1132_);
if (lean_obj_tag(v_info_1132_) == 0)
{
lean_object* v_val_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1145_; 
v_val_1133_ = lean_ctor_get(v_x_1126_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v_x_1126_, 0);
lean_dec(v_unused_1146_);
v___x_1135_ = v_x_1126_;
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_val_1133_);
lean_dec(v_x_1126_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1145_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_trailing_1137_; lean_object* v_trailStop_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v_trailing_1137_ = lean_ctor_get(v_info_1132_, 2);
v_trailStop_1138_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1137_);
lean_inc(v_trailStop_1138_);
v___x_1139_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1132_, v_a_1127_, v_trailStop_1138_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1139_);
v___x_1141_ = v___x_1135_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_val_1133_);
v___x_1141_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1142_);
lean_ctor_set(v___x_1143_, 1, v_trailStop_1138_);
return v___x_1143_;
}
}
}
else
{
lean_dec(v_info_1132_);
lean_dec_ref_known(v_x_1126_, 2);
v___y_1129_ = v_a_1127_;
goto v___jp_1128_;
}
}
case 3:
{
lean_object* v_info_1147_; 
v_info_1147_ = lean_ctor_get(v_x_1126_, 0);
lean_inc(v_info_1147_);
if (lean_obj_tag(v_info_1147_) == 0)
{
lean_object* v_rawVal_1148_; lean_object* v_val_1149_; lean_object* v_preresolved_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1162_; 
v_rawVal_1148_ = lean_ctor_get(v_x_1126_, 1);
v_val_1149_ = lean_ctor_get(v_x_1126_, 2);
v_preresolved_1150_ = lean_ctor_get(v_x_1126_, 3);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_x_1126_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_x_1126_, 0);
lean_dec(v_unused_1163_);
v___x_1152_ = v_x_1126_;
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_preresolved_1150_);
lean_inc(v_val_1149_);
lean_inc(v_rawVal_1148_);
lean_dec(v_x_1126_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_trailing_1154_; lean_object* v_trailStop_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v_trailing_1154_ = lean_ctor_get(v_info_1147_, 2);
v_trailStop_1155_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1154_);
lean_inc(v_trailStop_1155_);
v___x_1156_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1147_, v_a_1127_, v_trailStop_1155_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1156_);
v___x_1158_ = v___x_1152_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_rawVal_1148_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_val_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_preresolved_1150_);
v___x_1158_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1159_, 0, v___x_1158_);
v___x_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v_trailStop_1155_);
return v___x_1160_;
}
}
}
else
{
lean_dec(v_info_1147_);
lean_dec_ref_known(v_x_1126_, 4);
v___y_1129_ = v_a_1127_;
goto v___jp_1128_;
}
}
default: 
{
lean_dec(v_x_1126_);
v___y_1129_ = v_a_1127_;
goto v___jp_1128_;
}
}
v___jp_1128_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v___y_1129_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
switch(lean_obj_tag(v___y_1164_))
{
case 2:
{
lean_object* v_info_1169_; 
v_info_1169_ = lean_ctor_get(v___y_1164_, 0);
lean_inc(v_info_1169_);
if (lean_obj_tag(v_info_1169_) == 0)
{
lean_object* v_val_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1182_; 
v_val_1170_ = lean_ctor_get(v___y_1164_, 1);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___y_1164_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___y_1164_, 0);
lean_dec(v_unused_1183_);
v___x_1172_ = v___y_1164_;
v_isShared_1173_ = v_isSharedCheck_1182_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_val_1170_);
lean_dec(v___y_1164_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1182_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_trailing_1174_; lean_object* v_trailStop_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v_trailing_1174_ = lean_ctor_get(v_info_1169_, 2);
v_trailStop_1175_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1174_);
lean_inc(v_trailStop_1175_);
v___x_1176_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1169_, v___y_1165_, v_trailStop_1175_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1176_);
v___x_1178_ = v___x_1172_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_val_1170_);
v___x_1178_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v_trailStop_1175_);
return v___x_1180_;
}
}
}
else
{
lean_dec(v_info_1169_);
lean_dec_ref_known(v___y_1164_, 2);
goto v___jp_1166_;
}
}
case 3:
{
lean_object* v_info_1184_; 
v_info_1184_ = lean_ctor_get(v___y_1164_, 0);
lean_inc(v_info_1184_);
if (lean_obj_tag(v_info_1184_) == 0)
{
lean_object* v_rawVal_1185_; lean_object* v_val_1186_; lean_object* v_preresolved_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1199_; 
v_rawVal_1185_ = lean_ctor_get(v___y_1164_, 1);
v_val_1186_ = lean_ctor_get(v___y_1164_, 2);
v_preresolved_1187_ = lean_ctor_get(v___y_1164_, 3);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___y_1164_);
if (v_isSharedCheck_1199_ == 0)
{
lean_object* v_unused_1200_; 
v_unused_1200_ = lean_ctor_get(v___y_1164_, 0);
lean_dec(v_unused_1200_);
v___x_1189_ = v___y_1164_;
v_isShared_1190_ = v_isSharedCheck_1199_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_preresolved_1187_);
lean_inc(v_val_1186_);
lean_inc(v_rawVal_1185_);
lean_dec(v___y_1164_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1199_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_trailing_1191_; lean_object* v_trailStop_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v_trailing_1191_ = lean_ctor_get(v_info_1184_, 2);
v_trailStop_1192_ = l___private_Lean_Syntax_0__Lean_Syntax_chooseNiceTrailStop(v_trailing_1191_);
lean_inc(v_trailStop_1192_);
v___x_1193_ = l___private_Lean_Syntax_0__Lean_Syntax_updateInfo(v_info_1184_, v___y_1165_, v_trailStop_1192_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1193_);
v___x_1195_ = v___x_1189_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1198_, 1, v_rawVal_1185_);
lean_ctor_set(v_reuseFailAlloc_1198_, 2, v_val_1186_);
lean_ctor_set(v_reuseFailAlloc_1198_, 3, v_preresolved_1187_);
v___x_1195_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v_trailStop_1192_);
return v___x_1197_;
}
}
}
else
{
lean_dec_ref_known(v___y_1164_, 4);
lean_dec(v_info_1184_);
goto v___jp_1166_;
}
}
default: 
{
lean_dec(v___y_1164_);
goto v___jp_1166_;
}
}
v___jp_1166_:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
lean_ctor_set(v___x_1168_, 1, v___y_1165_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(lean_object* v_x_1201_, lean_object* v___y_1202_){
_start:
{
if (lean_obj_tag(v_x_1201_) == 1)
{
lean_object* v_info_1203_; lean_object* v_kind_1204_; lean_object* v_args_1205_; lean_object* v___x_1206_; lean_object* v_fst_1207_; 
v_info_1203_ = lean_ctor_get(v_x_1201_, 0);
lean_inc(v_info_1203_);
v_kind_1204_ = lean_ctor_get(v_x_1201_, 1);
lean_inc(v_kind_1204_);
v_args_1205_ = lean_ctor_get(v_x_1201_, 2);
lean_inc_ref(v_args_1205_);
v___x_1206_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1201_, v___y_1202_);
v_fst_1207_ = lean_ctor_get(v___x_1206_, 0);
if (lean_obj_tag(v_fst_1207_) == 0)
{
lean_object* v_snd_1208_; size_t v_sz_1209_; size_t v___x_1210_; lean_object* v___x_1211_; lean_object* v_fst_1212_; lean_object* v_snd_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_snd_1208_ = lean_ctor_get(v___x_1206_, 1);
lean_inc(v_snd_1208_);
lean_dec_ref(v___x_1206_);
v_sz_1209_ = lean_array_size(v_args_1205_);
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_1209_, v___x_1210_, v_args_1205_, v_snd_1208_);
v_fst_1212_ = lean_ctor_get(v___x_1211_, 0);
v_snd_1213_ = lean_ctor_get(v___x_1211_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v___x_1211_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_snd_1213_);
lean_inc(v_fst_1212_);
lean_dec(v___x_1211_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1217_, 0, v_info_1203_);
lean_ctor_set(v___x_1217_, 1, v_kind_1204_);
lean_ctor_set(v___x_1217_, 2, v_fst_1212_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_snd_1213_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_object* v_snd_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1230_; 
lean_inc_ref(v_fst_1207_);
lean_dec_ref(v_args_1205_);
lean_dec(v_kind_1204_);
lean_dec(v_info_1203_);
v_snd_1222_ = lean_ctor_get(v___x_1206_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1206_, 0);
lean_dec(v_unused_1231_);
v___x_1224_ = v___x_1206_;
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_snd_1222_);
lean_dec(v___x_1206_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1230_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_val_1226_; lean_object* v___x_1228_; 
v_val_1226_ = lean_ctor_get(v_fst_1207_, 0);
lean_inc(v_val_1226_);
lean_dec_ref_known(v_fst_1207_, 1);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v_val_1226_);
v___x_1228_ = v___x_1224_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_val_1226_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_snd_1222_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
else
{
lean_object* v___x_1232_; lean_object* v_fst_1233_; 
lean_inc(v_x_1201_);
v___x_1232_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0___lam__0(v_x_1201_, v___y_1202_);
v_fst_1233_ = lean_ctor_get(v___x_1232_, 0);
if (lean_obj_tag(v_fst_1233_) == 0)
{
lean_object* v_snd_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
v_snd_1234_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1242_);
v___x_1236_ = v___x_1232_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snd_1234_);
lean_dec(v___x_1232_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v_x_1201_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_x_1201_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_snd_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1251_; 
lean_inc_ref(v_fst_1233_);
lean_dec(v_x_1201_);
v_snd_1243_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1252_);
v___x_1245_ = v___x_1232_;
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_dec(v___x_1232_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1251_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_val_1247_; lean_object* v___x_1249_; 
v_val_1247_ = lean_ctor_get(v_fst_1233_, 0);
lean_inc(v_val_1247_);
lean_dec_ref_known(v_fst_1233_, 1);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_val_1247_);
v___x_1249_ = v___x_1245_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_val_1247_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_snd_1243_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(size_t v_sz_1253_, size_t v_i_1254_, lean_object* v_bs_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1254_, v_sz_1253_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_bs_1255_);
lean_ctor_set(v___x_1258_, 1, v___y_1256_);
return v___x_1258_;
}
else
{
lean_object* v_v_1259_; lean_object* v___x_1260_; lean_object* v_fst_1261_; lean_object* v_snd_1262_; lean_object* v___x_1263_; lean_object* v_bs_x27_1264_; size_t v___x_1265_; size_t v___x_1266_; lean_object* v___x_1267_; 
v_v_1259_ = lean_array_uget_borrowed(v_bs_1255_, v_i_1254_);
lean_inc(v_v_1259_);
v___x_1260_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_v_1259_, v___y_1256_);
v_fst_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_fst_1261_);
v_snd_1262_ = lean_ctor_get(v___x_1260_, 1);
lean_inc(v_snd_1262_);
lean_dec_ref(v___x_1260_);
v___x_1263_ = lean_unsigned_to_nat(0u);
v_bs_x27_1264_ = lean_array_uset(v_bs_1255_, v_i_1254_, v___x_1263_);
v___x_1265_ = ((size_t)1ULL);
v___x_1266_ = lean_usize_add(v_i_1254_, v___x_1265_);
v___x_1267_ = lean_array_uset(v_bs_x27_1264_, v_i_1254_, v_fst_1261_);
v_i_1254_ = v___x_1266_;
v_bs_1255_ = v___x_1267_;
v___y_1256_ = v_snd_1262_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0___boxed(lean_object* v_sz_1269_, lean_object* v_i_1270_, lean_object* v_bs_1271_, lean_object* v___y_1272_){
_start:
{
size_t v_sz_boxed_1273_; size_t v_i_boxed_1274_; lean_object* v_res_1275_; 
v_sz_boxed_1273_ = lean_unbox_usize(v_sz_1269_);
lean_dec(v_sz_1269_);
v_i_boxed_1274_ = lean_unbox_usize(v_i_1270_);
lean_dec(v_i_1270_);
v_res_1275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0_spec__0(v_sz_boxed_1273_, v_i_boxed_1274_, v_bs_1271_, v___y_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateLeading(lean_object* v_stx_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v_fst_1279_; 
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = l_Lean_Syntax_replaceM___at___00Lean_Syntax_updateLeading_spec__0(v_stx_1276_, v___x_1277_);
v_fst_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_fst_1279_);
lean_dec_ref(v___x_1278_);
return v_fst_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_updateTrailing(lean_object* v_trailing_1280_, lean_object* v_x_1281_){
_start:
{
switch(lean_obj_tag(v_x_1281_))
{
case 2:
{
lean_object* v_info_1282_; lean_object* v_val_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1291_; 
v_info_1282_ = lean_ctor_get(v_x_1281_, 0);
v_val_1283_ = lean_ctor_get(v_x_1281_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1285_ = v_x_1281_;
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_val_1283_);
lean_inc(v_info_1282_);
lean_dec(v_x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1291_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1280_, v_info_1282_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 0, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_val_1283_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
case 3:
{
lean_object* v_info_1292_; lean_object* v_rawVal_1293_; lean_object* v_val_1294_; lean_object* v_preresolved_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1303_; 
v_info_1292_ = lean_ctor_get(v_x_1281_, 0);
v_rawVal_1293_ = lean_ctor_get(v_x_1281_, 1);
v_val_1294_ = lean_ctor_get(v_x_1281_, 2);
v_preresolved_1295_ = lean_ctor_get(v_x_1281_, 3);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1297_ = v_x_1281_;
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_preresolved_1295_);
lean_inc(v_val_1294_);
lean_inc(v_rawVal_1293_);
lean_inc(v_info_1292_);
lean_dec(v_x_1281_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1303_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = l_Lean_SourceInfo_updateTrailing(v_trailing_1280_, v_info_1292_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_rawVal_1293_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_val_1294_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_preresolved_1295_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
case 1:
{
lean_object* v_info_1304_; lean_object* v_kind_1305_; lean_object* v_args_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_info_1304_ = lean_ctor_get(v_x_1281_, 0);
v_kind_1305_ = lean_ctor_get(v_x_1281_, 1);
v_args_1306_ = lean_ctor_get(v_x_1281_, 2);
v___x_1307_ = lean_array_get_size(v_args_1306_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_nat_dec_eq(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1321_; 
lean_inc_ref(v_args_1306_);
lean_inc(v_kind_1305_);
lean_inc(v_info_1304_);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_x_1281_);
if (v_isSharedCheck_1321_ == 0)
{
lean_object* v_unused_1322_; lean_object* v_unused_1323_; lean_object* v_unused_1324_; 
v_unused_1322_ = lean_ctor_get(v_x_1281_, 2);
lean_dec(v_unused_1322_);
v_unused_1323_ = lean_ctor_get(v_x_1281_, 1);
lean_dec(v_unused_1323_);
v_unused_1324_ = lean_ctor_get(v_x_1281_, 0);
lean_dec(v_unused_1324_);
v___x_1311_ = v_x_1281_;
v_isShared_1312_ = v_isSharedCheck_1321_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_x_1281_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1321_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v_i_1314_; lean_object* v___x_1315_; lean_object* v_last_1316_; lean_object* v_args_1317_; lean_object* v___x_1319_; 
v___x_1313_ = lean_unsigned_to_nat(1u);
v_i_1314_ = lean_nat_sub(v___x_1307_, v___x_1313_);
v___x_1315_ = lean_array_fget_borrowed(v_args_1306_, v_i_1314_);
lean_inc(v___x_1315_);
v_last_1316_ = l_Lean_Syntax_updateTrailing(v_trailing_1280_, v___x_1315_);
v_args_1317_ = lean_array_fset(v_args_1306_, v_i_1314_, v_last_1316_);
lean_dec(v_i_1314_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 2, v_args_1317_);
v___x_1319_ = v___x_1311_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_info_1304_);
lean_ctor_set(v_reuseFailAlloc_1320_, 1, v_kind_1305_);
lean_ctor_set(v_reuseFailAlloc_1320_, 2, v_args_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
else
{
lean_dec_ref(v_trailing_1280_);
return v_x_1281_;
}
}
default: 
{
lean_dec_ref(v_trailing_1280_);
return v_x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0___redArg(lean_object* v_a_1325_, lean_object* v_b_1326_){
_start:
{
lean_object* v_countdown_1327_; lean_object* v_inner_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1351_; 
v_countdown_1327_ = lean_ctor_get(v_a_1325_, 0);
v_inner_1328_ = lean_ctor_get(v_a_1325_, 1);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_a_1325_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1330_ = v_a_1325_;
v_isShared_1331_ = v_isSharedCheck_1351_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_inner_1328_);
lean_inc(v_countdown_1327_);
lean_dec(v_a_1325_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1351_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1332_; lean_object* v_it_1334_; lean_object* v_out_1335_; uint8_t v___x_1342_; 
v___x_1332_ = lean_unsigned_to_nat(1u);
v___x_1342_ = lean_nat_dec_eq(v_countdown_1327_, v___x_1332_);
if (v___x_1342_ == 0)
{
switch(lean_obj_tag(v_inner_1328_))
{
case 0:
{
lean_del_object(v___x_1330_);
lean_dec(v_countdown_1327_);
return v_b_1326_;
}
case 1:
{
lean_object* v_pre_1343_; lean_object* v_str_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_pre_1343_ = lean_ctor_get(v_inner_1328_, 0);
lean_inc(v_pre_1343_);
v_str_1344_ = lean_ctor_get(v_inner_1328_, 1);
lean_inc_ref(v_str_1344_);
lean_dec_ref_known(v_inner_1328_, 2);
v___x_1345_ = lean_box(0);
v___x_1346_ = l_Lean_Name_str___override(v___x_1345_, v_str_1344_);
v_it_1334_ = v_pre_1343_;
v_out_1335_ = v___x_1346_;
goto v___jp_1333_;
}
default: 
{
lean_object* v_pre_1347_; lean_object* v_i_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_pre_1347_ = lean_ctor_get(v_inner_1328_, 0);
lean_inc(v_pre_1347_);
v_i_1348_ = lean_ctor_get(v_inner_1328_, 1);
lean_inc(v_i_1348_);
lean_dec_ref_known(v_inner_1328_, 2);
v___x_1349_ = lean_box(0);
v___x_1350_ = l_Lean_Name_num___override(v___x_1349_, v_i_1348_);
v_it_1334_ = v_pre_1347_;
v_out_1335_ = v___x_1350_;
goto v___jp_1333_;
}
}
}
else
{
lean_del_object(v___x_1330_);
lean_dec(v_inner_1328_);
lean_dec(v_countdown_1327_);
return v_b_1326_;
}
v___jp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1336_ = lean_nat_sub(v_countdown_1327_, v___x_1332_);
lean_dec(v_countdown_1327_);
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v_it_1334_);
lean_ctor_set(v___x_1330_, 0, v___x_1336_);
v___x_1338_ = v___x_1330_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1336_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_it_1334_);
v___x_1338_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1339_, 0, v_out_1335_);
lean_ctor_set(v___x_1339_, 1, v_b_1326_);
v_a_1325_ = v___x_1338_;
v_b_1326_ = v___x_1339_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(lean_object* v_n_1352_, lean_object* v_nFields_x3f_1353_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1353_) == 1)
{
lean_object* v_val_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_val_1354_ = lean_ctor_get(v_nFields_x3f_1353_, 0);
lean_inc_n(v_val_1354_, 2);
lean_dec_ref_known(v_nFields_x3f_1353_, 1);
v___x_1355_ = l_Lean_Name_dropLastComponents(v_n_1352_, v_val_1354_);
v___x_1356_ = l_Lean_Name_revIter(v_n_1352_);
lean_dec(v_n_1352_);
v___x_1357_ = lean_unsigned_to_nat(1u);
v___x_1358_ = lean_nat_add(v_val_1354_, v___x_1357_);
lean_dec(v_val_1354_);
v___x_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v___x_1356_);
v___x_1360_ = lean_box(0);
v___x_1361_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0___redArg(v___x_1359_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1355_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
return v___x_1362_;
}
else
{
lean_object* v___x_1363_; 
lean_dec(v_nFields_x3f_1353_);
v___x_1363_ = l_Lean_Name_components(v_n_1352_);
return v___x_1363_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0(lean_object* v_inst_1364_, lean_object* v_R_1365_, lean_object* v_a_1366_, lean_object* v_b_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0___redArg(v_a_1366_, v_b_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(lean_object* v_msg_1369_){
_start:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_panic_fn_borrowed(v___x_1370_, v_msg_1369_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f___lam__0(lean_object* v_fst_1372_, lean_object* v_snd_1373_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_fst_1372_);
lean_ctor_set(v___x_1374_, 1, v_snd_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(lean_object* v_x_1375_, lean_object* v_x_1376_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
return v_x_1375_;
}
else
{
lean_object* v_head_1377_; lean_object* v_tail_1378_; lean_object* v_startPos_1379_; lean_object* v_stopPos_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_head_1377_ = lean_ctor_get(v_x_1376_, 0);
v_tail_1378_ = lean_ctor_get(v_x_1376_, 1);
v_startPos_1379_ = lean_ctor_get(v_head_1377_, 1);
v_stopPos_1380_ = lean_ctor_get(v_head_1377_, 2);
v___x_1381_ = lean_nat_sub(v_stopPos_1380_, v_startPos_1379_);
v___x_1382_ = lean_nat_add(v_x_1375_, v___x_1381_);
lean_dec(v___x_1381_);
lean_dec(v_x_1375_);
v___x_1383_ = lean_unsigned_to_nat(1u);
v___x_1384_ = lean_nat_add(v___x_1382_, v___x_1383_);
lean_dec(v___x_1382_);
v_x_1375_ = v___x_1384_;
v_x_1376_ = v_tail_1378_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2___boxed(lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v_x_1386_, v_x_1387_);
lean_dec(v_x_1387_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(lean_object* v_rawVal_1393_, lean_object* v_pos_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_){
_start:
{
if (lean_obj_tag(v_a_1395_) == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = l_List_reverse___redArg(v_a_1396_);
return v___x_1397_;
}
else
{
lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1417_; 
v_head_1398_ = lean_ctor_get(v_a_1395_, 0);
v_tail_1399_ = lean_ctor_get(v_a_1395_, 1);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_a_1395_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1401_ = v_a_1395_;
v_isShared_1402_ = v_isSharedCheck_1417_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_tail_1399_);
lean_inc(v_head_1398_);
lean_dec(v_a_1395_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1417_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_stopPos_1403_; lean_object* v_startPos_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v_info_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v_stopPos_1403_ = lean_ctor_get(v_head_1398_, 2);
lean_inc(v_stopPos_1403_);
lean_dec(v_head_1398_);
v_startPos_1404_ = lean_ctor_get(v_rawVal_1393_, 1);
v___x_1405_ = lean_nat_sub(v_stopPos_1403_, v_startPos_1404_);
lean_dec(v_stopPos_1403_);
v___x_1406_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___x_1407_ = lean_nat_add(v___x_1405_, v_pos_1394_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_nat_add(v___x_1408_, v___x_1407_);
v_info_1410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1410_, 0, v___x_1406_);
lean_ctor_set(v_info_1410_, 1, v___x_1407_);
lean_ctor_set(v_info_1410_, 2, v___x_1406_);
lean_ctor_set(v_info_1410_, 3, v___x_1409_);
v___x_1411_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__1));
v___x_1412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_info_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v_a_1396_);
lean_ctor_set(v___x_1401_, 0, v___x_1412_);
v___x_1414_ = v___x_1401_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_a_1396_);
v___x_1414_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
v_a_1395_ = v_tail_1399_;
v_a_1396_ = v___x_1414_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___boxed(lean_object* v_rawVal_1418_, lean_object* v_pos_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1418_, v_pos_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_pos_1419_);
lean_dec_ref(v_rawVal_1418_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(lean_object* v_rawVal_1423_, lean_object* v_pos_1424_, lean_object* v_trailing_1425_, lean_object* v_leading_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_){
_start:
{
if (lean_obj_tag(v_a_1427_) == 0)
{
lean_object* v___x_1429_; 
lean_dec_ref(v_leading_1426_);
lean_dec_ref(v_trailing_1425_);
v___x_1429_ = l_List_reverse___redArg(v_a_1428_);
return v___x_1429_;
}
else
{
lean_object* v_head_1430_; lean_object* v_snd_1431_; lean_object* v_tail_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1462_; 
v_head_1430_ = lean_ctor_get(v_a_1427_, 0);
lean_inc(v_head_1430_);
v_snd_1431_ = lean_ctor_get(v_head_1430_, 1);
lean_inc(v_snd_1431_);
v_tail_1432_ = lean_ctor_get(v_a_1427_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_a_1427_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v_a_1427_, 0);
lean_dec(v_unused_1463_);
v___x_1434_ = v_a_1427_;
v_isShared_1435_ = v_isSharedCheck_1462_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_tail_1432_);
lean_dec(v_a_1427_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1462_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_fst_1436_; lean_object* v_startPos_1437_; lean_object* v_stopPos_1438_; lean_object* v_startPos_1439_; lean_object* v_stopPos_1440_; lean_object* v_off_1441_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1456_; lean_object* v___x_1459_; uint8_t v_decide_1460_; 
v_fst_1436_ = lean_ctor_get(v_head_1430_, 0);
lean_inc(v_fst_1436_);
lean_dec(v_head_1430_);
v_startPos_1437_ = lean_ctor_get(v_snd_1431_, 1);
v_stopPos_1438_ = lean_ctor_get(v_snd_1431_, 2);
v_startPos_1439_ = lean_ctor_get(v_rawVal_1423_, 1);
v_stopPos_1440_ = lean_ctor_get(v_rawVal_1423_, 2);
v_off_1441_ = lean_nat_sub(v_startPos_1437_, v_startPos_1439_);
v___x_1459_ = lean_unsigned_to_nat(0u);
v_decide_1460_ = lean_nat_dec_eq(v_off_1441_, v___x_1459_);
if (v_decide_1460_ == 0)
{
lean_object* v___x_1461_; 
v___x_1461_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1456_ = v___x_1461_;
goto v___jp_1455_;
}
else
{
lean_inc_ref(v_leading_1426_);
v___y_1456_ = v_leading_1426_;
goto v___jp_1455_;
}
v___jp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_info_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1445_ = lean_nat_add(v_off_1441_, v_pos_1424_);
lean_dec(v_off_1441_);
v___x_1446_ = lean_nat_sub(v_stopPos_1438_, v_startPos_1437_);
v___x_1447_ = lean_nat_add(v___x_1446_, v___x_1445_);
lean_dec(v___x_1446_);
v_info_1448_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_info_1448_, 0, v___y_1443_);
lean_ctor_set(v_info_1448_, 1, v___x_1445_);
lean_ctor_set(v_info_1448_, 2, v___y_1444_);
lean_ctor_set(v_info_1448_, 3, v___x_1447_);
v___x_1449_ = lean_box(0);
v___x_1450_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1450_, 0, v_info_1448_);
lean_ctor_set(v___x_1450_, 1, v_snd_1431_);
lean_ctor_set(v___x_1450_, 2, v_fst_1436_);
lean_ctor_set(v___x_1450_, 3, v___x_1449_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 1, v_a_1428_);
lean_ctor_set(v___x_1434_, 0, v___x_1450_);
v___x_1452_ = v___x_1434_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_a_1428_);
v___x_1452_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v_a_1427_ = v_tail_1432_;
v_a_1428_ = v___x_1452_;
goto _start;
}
}
v___jp_1455_:
{
uint8_t v_decide_1457_; 
v_decide_1457_ = lean_nat_dec_eq(v_stopPos_1438_, v_stopPos_1440_);
if (v_decide_1457_ == 0)
{
lean_object* v___x_1458_; 
v___x_1458_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1443_ = v___y_1456_;
v___y_1444_ = v___x_1458_;
goto v___jp_1442_;
}
else
{
lean_inc_ref(v_trailing_1425_);
v___y_1443_ = v___y_1456_;
v___y_1444_ = v_trailing_1425_;
goto v___jp_1442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0___boxed(lean_object* v_rawVal_1464_, lean_object* v_pos_1465_, lean_object* v_trailing_1466_, lean_object* v_leading_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1464_, v_pos_1465_, v_trailing_1466_, v_leading_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_pos_1465_);
lean_dec_ref(v_rawVal_1464_);
return v_res_1470_;
}
}
static lean_object* _init_l_Lean_Syntax_identComponents_x3f___closed__6(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1479_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__5));
v___x_1480_ = lean_unsigned_to_nat(9u);
v___x_1481_ = lean_unsigned_to_nat(358u);
v___x_1482_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__4));
v___x_1483_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1484_ = l_mkPanicMessageWithDecl(v___x_1483_, v___x_1482_, v___x_1481_, v___x_1480_, v___x_1479_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents_x3f(lean_object* v_stx_1485_, lean_object* v_nFields_x3f_1486_){
_start:
{
if (lean_obj_tag(v_stx_1485_) == 3)
{
lean_object* v_info_1487_; 
v_info_1487_ = lean_ctor_get(v_stx_1485_, 0);
lean_inc(v_info_1487_);
if (lean_obj_tag(v_info_1487_) == 0)
{
lean_object* v_rawVal_1488_; lean_object* v_val_1489_; lean_object* v_leading_1490_; lean_object* v_pos_1491_; lean_object* v_trailing_1492_; lean_object* v_rawComps_1493_; uint8_t v___x_1494_; 
v_rawVal_1488_ = lean_ctor_get(v_stx_1485_, 1);
lean_inc_ref_n(v_rawVal_1488_, 2);
v_val_1489_ = lean_ctor_get(v_stx_1485_, 2);
lean_inc(v_val_1489_);
lean_dec_ref_known(v_stx_1485_, 4);
v_leading_1490_ = lean_ctor_get(v_info_1487_, 0);
lean_inc_ref(v_leading_1490_);
v_pos_1491_ = lean_ctor_get(v_info_1487_, 1);
lean_inc(v_pos_1491_);
v_trailing_1492_ = lean_ctor_get(v_info_1487_, 2);
lean_inc_ref(v_trailing_1492_);
lean_dec_ref_known(v_info_1487_, 4);
v_rawComps_1493_ = l_Lean_Syntax_splitNameLit(v_rawVal_1488_);
v___x_1494_ = l_List_isEmpty___redArg(v_rawComps_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___f_1495_; lean_object* v_val_1496_; lean_object* v_nameComps_1497_; lean_object* v___y_1499_; 
v___f_1495_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__0));
v_val_1496_ = l_Lean_Name_eraseMacroScopes(v_val_1489_);
lean_dec(v_val_1489_);
lean_inc(v_nFields_x3f_1486_);
v_nameComps_1497_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps(v_val_1496_, v_nFields_x3f_1486_);
if (lean_obj_tag(v_nFields_x3f_1486_) == 1)
{
lean_object* v_val_1514_; lean_object* v_str_1515_; lean_object* v_startPos_1516_; lean_object* v_stopPos_1517_; lean_object* v___x_1518_; lean_object* v_nPrefix_1519_; lean_object* v___y_1521_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v_prefixSz_1527_; lean_object* v___x_1528_; lean_object* v_prefixSz_1529_; lean_object* v___y_1531_; uint8_t v___x_1536_; 
v_val_1514_ = lean_ctor_get(v_nFields_x3f_1486_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v_nFields_x3f_1486_, 1);
v_str_1515_ = lean_ctor_get(v_rawVal_1488_, 0);
v_startPos_1516_ = lean_ctor_get(v_rawVal_1488_, 1);
v_stopPos_1517_ = lean_ctor_get(v_rawVal_1488_, 2);
v___x_1518_ = l_List_lengthTR___redArg(v_rawComps_1493_);
v_nPrefix_1519_ = lean_nat_sub(v___x_1518_, v_val_1514_);
lean_dec(v_val_1514_);
lean_dec(v___x_1518_);
v___x_1524_ = lean_unsigned_to_nat(0u);
v___x_1525_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__2));
lean_inc(v_nPrefix_1519_);
lean_inc(v_rawComps_1493_);
v___x_1526_ = l___private_Init_Data_List_Impl_0__List_takeTR_go(lean_box(0), v_rawComps_1493_, v_rawComps_1493_, v_nPrefix_1519_, v___x_1525_);
v_prefixSz_1527_ = l_List_foldl___at___00Lean_Syntax_identComponents_x3f_spec__2(v___x_1524_, v___x_1526_);
lean_dec(v___x_1526_);
v___x_1528_ = lean_unsigned_to_nat(1u);
v_prefixSz_1529_ = lean_nat_sub(v_prefixSz_1527_, v___x_1528_);
lean_dec(v_prefixSz_1527_);
v___x_1536_ = lean_nat_dec_le(v_prefixSz_1529_, v___x_1524_);
if (v___x_1536_ == 0)
{
uint8_t v___x_1537_; 
v___x_1537_ = lean_nat_dec_le(v_stopPos_1517_, v_startPos_1516_);
if (v___x_1537_ == 0)
{
lean_inc(v_startPos_1516_);
v___y_1531_ = v_startPos_1516_;
goto v___jp_1530_;
}
else
{
lean_inc(v_stopPos_1517_);
v___y_1531_ = v_stopPos_1517_;
goto v___jp_1530_;
}
}
else
{
lean_object* v___x_1538_; 
lean_dec(v_prefixSz_1529_);
v___x_1538_ = ((lean_object*)(l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1___closed__0));
v___y_1521_ = v___x_1538_;
goto v___jp_1520_;
}
v___jp_1520_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = l_List_drop___redArg(v_nPrefix_1519_, v_rawComps_1493_);
lean_dec(v_rawComps_1493_);
v___x_1523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___y_1521_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___y_1499_ = v___x_1523_;
goto v___jp_1498_;
}
v___jp_1530_:
{
lean_object* v___x_1532_; uint8_t v___x_1533_; 
v___x_1532_ = lean_nat_add(v_startPos_1516_, v_prefixSz_1529_);
lean_dec(v_prefixSz_1529_);
v___x_1533_ = lean_nat_dec_le(v_stopPos_1517_, v___x_1532_);
if (v___x_1533_ == 0)
{
lean_object* v___x_1534_; 
lean_inc_ref(v_str_1515_);
v___x_1534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1534_, 0, v_str_1515_);
lean_ctor_set(v___x_1534_, 1, v___y_1531_);
lean_ctor_set(v___x_1534_, 2, v___x_1532_);
v___y_1521_ = v___x_1534_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1535_; 
lean_dec(v___x_1532_);
lean_inc(v_stopPos_1517_);
lean_inc_ref(v_str_1515_);
v___x_1535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1535_, 0, v_str_1515_);
lean_ctor_set(v___x_1535_, 1, v___y_1531_);
lean_ctor_set(v___x_1535_, 2, v_stopPos_1517_);
v___y_1521_ = v___x_1535_;
goto v___jp_1520_;
}
}
}
else
{
lean_dec(v_nFields_x3f_1486_);
v___y_1499_ = v_rawComps_1493_;
goto v___jp_1498_;
}
v___jp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1500_ = l_List_lengthTR___redArg(v_nameComps_1497_);
v___x_1501_ = l_List_lengthTR___redArg(v___y_1499_);
v___x_1502_ = lean_nat_dec_eq(v___x_1500_, v___x_1501_);
lean_dec(v___x_1501_);
lean_dec(v___x_1500_);
if (v___x_1502_ == 0)
{
lean_object* v___x_1503_; 
lean_dec(v___y_1499_);
lean_dec(v_nameComps_1497_);
lean_dec_ref(v_trailing_1492_);
lean_dec(v_pos_1491_);
lean_dec_ref(v_leading_1490_);
lean_dec_ref(v_rawVal_1488_);
v___x_1503_ = lean_box(0);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_comps_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v_seps_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1504_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__1));
lean_inc(v___y_1499_);
v___x_1505_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_1495_, v_nameComps_1497_, v___y_1499_, v___x_1504_);
v___x_1506_ = lean_box(0);
v_comps_1507_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__0(v_rawVal_1488_, v_pos_1491_, v_trailing_1492_, v_leading_1490_, v___x_1505_, v___x_1506_);
v___x_1508_ = lean_array_mk(v___y_1499_);
v___x_1509_ = lean_array_pop(v___x_1508_);
v___x_1510_ = lean_array_to_list(v___x_1509_);
v_seps_1511_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_x3f_spec__1(v_rawVal_1488_, v_pos_1491_, v___x_1510_, v___x_1506_);
lean_dec(v_pos_1491_);
lean_dec_ref(v_rawVal_1488_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v_comps_1507_);
lean_ctor_set(v___x_1512_, 1, v_seps_1511_);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
}
else
{
lean_object* v___x_1539_; 
lean_dec(v_rawComps_1493_);
lean_dec_ref(v_trailing_1492_);
lean_dec(v_pos_1491_);
lean_dec_ref(v_leading_1490_);
lean_dec(v_val_1489_);
lean_dec_ref(v_rawVal_1488_);
lean_dec(v_nFields_x3f_1486_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
}
else
{
lean_object* v___x_1540_; 
lean_dec_ref_known(v_stx_1485_, 4);
lean_dec(v_info_1487_);
lean_dec(v_nFields_x3f_1486_);
v___x_1540_ = lean_box(0);
return v___x_1540_;
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_dec(v_nFields_x3f_1486_);
lean_dec(v_stx_1485_);
v___x_1541_ = lean_obj_once(&l_Lean_Syntax_identComponents_x3f___closed__6, &l_Lean_Syntax_identComponents_x3f___closed__6_once, _init_l_Lean_Syntax_identComponents_x3f___closed__6);
v___x_1542_ = l_panic___at___00Lean_Syntax_identComponents_x3f_spec__3(v___x_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(lean_object* v_n_1543_, lean_object* v_nFields_x3f_1544_){
_start:
{
if (lean_obj_tag(v_nFields_x3f_1544_) == 1)
{
lean_object* v_val_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_val_1545_ = lean_ctor_get(v_nFields_x3f_1544_, 0);
lean_inc_n(v_val_1545_, 2);
lean_dec_ref_known(v_nFields_x3f_1544_, 1);
v___x_1546_ = l_Lean_Name_dropLastComponents(v_n_1543_, v_val_1545_);
v___x_1547_ = l_Lean_Name_revIter(v_n_1543_);
lean_dec(v_n_1543_);
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_nat_add(v_val_1545_, v___x_1548_);
lean_dec(v_val_1545_);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v___x_1547_);
v___x_1551_ = lean_box(0);
v___x_1552_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Syntax_0__Lean_Syntax_identComponents_x3f_nameComps_spec__0___redArg(v___x_1550_, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1546_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; 
lean_dec(v_nFields_x3f_1544_);
v___x_1554_ = l_Lean_Name_components(v_n_1543_);
return v___x_1554_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Syntax_identComponents_spec__1(lean_object* v_msg_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_panic_fn_borrowed(v___x_1556_, v_msg_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(lean_object* v_info_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
if (lean_obj_tag(v_a_1559_) == 0)
{
lean_object* v___x_1561_; 
lean_dec(v_info_1558_);
v___x_1561_ = l_List_reverse___redArg(v_a_1560_);
return v___x_1561_;
}
else
{
lean_object* v_head_1562_; lean_object* v_tail_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1578_; 
v_head_1562_ = lean_ctor_get(v_a_1559_, 0);
v_tail_1563_ = lean_ctor_get(v_a_1559_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_a_1559_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1565_ = v_a_1559_;
v_isShared_1566_ = v_isSharedCheck_1578_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_tail_1563_);
lean_inc(v_head_1562_);
lean_dec(v_a_1559_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1578_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1567_ = 1;
lean_inc(v_head_1562_);
v___x_1568_ = l_Lean_Name_toString(v_head_1562_, v___x_1567_);
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = lean_string_utf8_byte_size(v___x_1568_);
v___x_1571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1568_);
lean_ctor_set(v___x_1571_, 1, v___x_1569_);
lean_ctor_set(v___x_1571_, 2, v___x_1570_);
v___x_1572_ = lean_box(0);
lean_inc(v_info_1558_);
v___x_1573_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1573_, 0, v_info_1558_);
lean_ctor_set(v___x_1573_, 1, v___x_1571_);
lean_ctor_set(v___x_1573_, 2, v_head_1562_);
lean_ctor_set(v___x_1573_, 3, v___x_1572_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v_a_1560_);
lean_ctor_set(v___x_1565_, 0, v___x_1573_);
v___x_1575_ = v___x_1565_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_a_1560_);
v___x_1575_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
v_a_1559_ = v_tail_1563_;
v_a_1560_ = v___x_1575_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Syntax_identComponents___closed__1(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1580_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__5));
v___x_1581_ = lean_unsigned_to_nat(9u);
v___x_1582_ = lean_unsigned_to_nat(390u);
v___x_1583_ = ((lean_object*)(l_Lean_Syntax_identComponents___closed__0));
v___x_1584_ = ((lean_object*)(l_Lean_Syntax_identComponents_x3f___closed__3));
v___x_1585_ = l_mkPanicMessageWithDecl(v___x_1584_, v___x_1583_, v___x_1582_, v___x_1581_, v___x_1580_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_identComponents(lean_object* v_stx_1586_, lean_object* v_nFields_x3f_1587_){
_start:
{
if (lean_obj_tag(v_stx_1586_) == 3)
{
lean_object* v_info_1588_; lean_object* v_rawVal_1589_; lean_object* v_val_1590_; lean_object* v_val_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v_info_1588_ = lean_ctor_get(v_stx_1586_, 0);
lean_inc(v_info_1588_);
v_rawVal_1589_ = lean_ctor_get(v_stx_1586_, 1);
v_val_1590_ = lean_ctor_get(v_stx_1586_, 2);
v_val_1591_ = l_Lean_Name_eraseMacroScopes(v_val_1590_);
v___x_1592_ = l_Lean_Name_getNumParts(v_val_1591_);
v___x_1593_ = lean_unsigned_to_nat(1u);
v___x_1594_ = lean_nat_dec_le(v___x_1592_, v___x_1593_);
lean_dec(v___x_1592_);
if (v___x_1594_ == 0)
{
if (lean_obj_tag(v_info_1588_) == 0)
{
lean_object* v___x_1595_; 
lean_inc(v_nFields_x3f_1587_);
v___x_1595_ = l_Lean_Syntax_identComponents_x3f(v_stx_1586_, v_nFields_x3f_1587_);
if (lean_obj_tag(v___x_1595_) == 1)
{
lean_object* v_val_1596_; lean_object* v_fst_1597_; 
lean_dec_ref_known(v_info_1588_, 4);
lean_dec(v_val_1591_);
lean_dec(v_nFields_x3f_1587_);
v_val_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_val_1596_);
lean_dec_ref_known(v___x_1595_, 1);
v_fst_1597_ = lean_ctor_get(v_val_1596_, 0);
lean_inc(v_fst_1597_);
lean_dec(v_val_1596_);
return v_fst_1597_;
}
else
{
lean_object* v_nameComps_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec(v___x_1595_);
v_nameComps_1598_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1591_, v_nFields_x3f_1587_);
v___x_1599_ = lean_box(0);
v___x_1600_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1588_, v_nameComps_1598_, v___x_1599_);
return v___x_1600_;
}
}
else
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec_ref_known(v_stx_1586_, 4);
v___x_1601_ = l___private_Lean_Syntax_0__Lean_Syntax_identComponents_nameComps(v_val_1591_, v_nFields_x3f_1587_);
v___x_1602_ = lean_box(0);
v___x_1603_ = l_List_mapTR_loop___at___00Lean_Syntax_identComponents_spec__0(v_info_1588_, v___x_1601_, v___x_1602_);
return v___x_1603_;
}
}
else
{
lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1612_; 
lean_inc_ref(v_rawVal_1589_);
lean_dec(v_nFields_x3f_1587_);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_stx_1586_);
if (v_isSharedCheck_1612_ == 0)
{
lean_object* v_unused_1613_; lean_object* v_unused_1614_; lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1613_ = lean_ctor_get(v_stx_1586_, 3);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_stx_1586_, 2);
lean_dec(v_unused_1614_);
v_unused_1615_ = lean_ctor_get(v_stx_1586_, 1);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_stx_1586_, 0);
lean_dec(v_unused_1616_);
v___x_1605_ = v_stx_1586_;
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
else
{
lean_dec(v_stx_1586_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1612_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1609_; 
v___x_1607_ = lean_box(0);
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 3, v___x_1607_);
lean_ctor_set(v___x_1605_, 2, v_val_1591_);
v___x_1609_ = v___x_1605_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_info_1588_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_rawVal_1589_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_val_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v___x_1607_);
v___x_1609_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1607_);
return v___x_1610_;
}
}
}
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec(v_nFields_x3f_1587_);
lean_dec(v_stx_1586_);
v___x_1617_ = lean_obj_once(&l_Lean_Syntax_identComponents___closed__1, &l_Lean_Syntax_identComponents___closed__1_once, _init_l_Lean_Syntax_identComponents___closed__1);
v___x_1618_ = l_panic___at___00Lean_Syntax_identComponents_spec__1(v___x_1617_);
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown(lean_object* v_stx_1619_, uint8_t v_firstChoiceOnly_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1621_, 0, v_stx_1619_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*1, v_firstChoiceOnly_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_topDown___boxed(lean_object* v_stx_1622_, lean_object* v_firstChoiceOnly_1623_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1624_; lean_object* v_res_1625_; 
v_firstChoiceOnly_boxed_1624_ = lean_unbox(v_firstChoiceOnly_1623_);
v_res_1625_ = l_Lean_Syntax_topDown(v_stx_1622_, v_firstChoiceOnly_boxed_1624_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0(lean_object* v_toPure_1626_, lean_object* v_____r_1627_, lean_object* v_b_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1629_, 0, v_b_1628_);
v___x_1630_ = lean_apply_2(v_toPure_1626_, lean_box(0), v___x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1(lean_object* v___f_1631_, lean_object* v_toPure_1632_, lean_object* v_____s_1633_){
_start:
{
lean_object* v_fst_1634_; 
v_fst_1634_ = lean_ctor_get(v_____s_1633_, 0);
if (lean_obj_tag(v_fst_1634_) == 0)
{
lean_object* v_snd_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec(v_toPure_1632_);
v_snd_1635_ = lean_ctor_get(v_____s_1633_, 1);
lean_inc(v_snd_1635_);
lean_dec_ref(v_____s_1633_);
v___x_1636_ = lean_box(0);
v___x_1637_ = lean_apply_2(v___f_1631_, v___x_1636_, v_snd_1635_);
return v___x_1637_;
}
else
{
lean_object* v_val_1638_; lean_object* v___x_1639_; 
lean_inc_ref(v_fst_1634_);
lean_dec_ref(v_____s_1633_);
lean_dec(v___f_1631_);
v_val_1638_ = lean_ctor_get(v_fst_1634_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v_fst_1634_, 1);
v___x_1639_ = lean_apply_2(v_toPure_1632_, lean_box(0), v_val_1638_);
return v___x_1639_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2(lean_object* v_snd_1640_, lean_object* v_toPure_1641_, lean_object* v___x_1642_, lean_object* v_____do__lift_1643_){
_start:
{
if (lean_obj_tag(v_____do__lift_1643_) == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec(v___x_1642_);
v___x_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1644_, 0, v_____do__lift_1643_);
v___x_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_snd_1640_);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
v___x_1647_ = lean_apply_2(v_toPure_1641_, lean_box(0), v___x_1646_);
return v___x_1647_;
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_snd_1640_);
v_a_1648_ = lean_ctor_get(v_____do__lift_1643_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_____do__lift_1643_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1650_ = v_____do__lift_1643_;
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v_____do__lift_1643_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1657_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1642_);
lean_ctor_set(v___x_1652_, 1, v_a_1648_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 0, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_apply_2(v_toPure_1641_, lean_box(0), v___x_1654_);
return v___x_1655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed(lean_object* v_toPure_1658_, lean_object* v___x_1659_, lean_object* v_inst_1660_, lean_object* v_f_1661_, lean_object* v_firstChoiceOnly_1662_, lean_object* v_toBind_1663_, lean_object* v_a_1664_, lean_object* v_x_1665_, lean_object* v___y_1666_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1667_; lean_object* v_res_1668_; 
v_firstChoiceOnly_boxed_1667_ = lean_unbox(v_firstChoiceOnly_1662_);
v_res_1668_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(v_toPure_1658_, v___x_1659_, v_inst_1660_, v_f_1661_, v_firstChoiceOnly_boxed_1667_, v_toBind_1663_, v_a_1664_, v_x_1665_, v___y_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(lean_object* v_toPure_1672_, lean_object* v_stx_1673_, lean_object* v_inst_1674_, lean_object* v_f_1675_, uint8_t v_firstChoiceOnly_1676_, lean_object* v_toBind_1677_, lean_object* v___f_1678_, lean_object* v___x_1679_, lean_object* v___f_1680_, lean_object* v_____do__lift_1681_){
_start:
{
if (lean_obj_tag(v_____do__lift_1681_) == 0)
{
lean_object* v___x_1682_; 
lean_dec(v___f_1680_);
lean_dec(v___f_1678_);
lean_dec(v_toBind_1677_);
lean_dec(v_f_1675_);
lean_dec_ref(v_inst_1674_);
lean_dec(v_stx_1673_);
v___x_1682_ = lean_apply_2(v_toPure_1672_, lean_box(0), v_____do__lift_1681_);
return v___x_1682_;
}
else
{
if (lean_obj_tag(v_stx_1673_) == 1)
{
lean_object* v_a_1683_; lean_object* v_kind_1684_; lean_object* v_args_1685_; 
lean_dec(v___f_1680_);
v_a_1683_ = lean_ctor_get(v_____do__lift_1681_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v_____do__lift_1681_, 1);
v_kind_1684_ = lean_ctor_get(v_stx_1673_, 1);
lean_inc(v_kind_1684_);
v_args_1685_ = lean_ctor_get(v_stx_1673_, 2);
lean_inc_ref(v_args_1685_);
lean_dec_ref_known(v_stx_1673_, 3);
if (v_firstChoiceOnly_1676_ == 0)
{
lean_dec(v_kind_1684_);
goto v___jp_1686_;
}
else
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1696_ = lean_name_eq(v_kind_1684_, v___x_1695_);
lean_dec(v_kind_1684_);
if (v___x_1696_ == 0)
{
goto v___jp_1686_;
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec(v___f_1678_);
lean_dec(v_toBind_1677_);
lean_dec(v_toPure_1672_);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_array_get(v___x_1679_, v_args_1685_, v___x_1697_);
lean_dec_ref(v_args_1685_);
v___x_1699_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1674_, v_f_1675_, v_firstChoiceOnly_1676_, v___x_1698_, v_a_1683_);
return v___x_1699_;
}
}
v___jp_1686_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; size_t v_sz_1691_; size_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1687_ = lean_box(0);
v___x_1688_ = lean_box(v_firstChoiceOnly_1676_);
lean_inc(v_toBind_1677_);
lean_inc_ref(v_inst_1674_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3___boxed), 9, 6);
lean_closure_set(v___f_1689_, 0, v_toPure_1672_);
lean_closure_set(v___f_1689_, 1, v___x_1687_);
lean_closure_set(v___f_1689_, 2, v_inst_1674_);
lean_closure_set(v___f_1689_, 3, v_f_1675_);
lean_closure_set(v___f_1689_, 4, v___x_1688_);
lean_closure_set(v___f_1689_, 5, v_toBind_1677_);
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1687_);
lean_ctor_set(v___x_1690_, 1, v_a_1683_);
v_sz_1691_ = lean_array_size(v_args_1685_);
v___x_1692_ = ((size_t)0ULL);
v___x_1693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1674_, v_args_1685_, v___f_1689_, v_sz_1691_, v___x_1692_, v___x_1690_);
v___x_1694_ = lean_apply_4(v_toBind_1677_, lean_box(0), lean_box(0), v___x_1693_, v___f_1678_);
return v___x_1694_;
}
}
else
{
lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec(v___f_1678_);
lean_dec(v_toBind_1677_);
lean_dec(v_f_1675_);
lean_dec_ref(v_inst_1674_);
lean_dec(v_stx_1673_);
lean_dec(v_toPure_1672_);
v_a_1700_ = lean_ctor_get(v_____do__lift_1681_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v_____do__lift_1681_, 1);
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_apply_2(v___f_1680_, v___x_1701_, v_a_1700_);
return v___x_1702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed(lean_object* v_toPure_1703_, lean_object* v_stx_1704_, lean_object* v_inst_1705_, lean_object* v_f_1706_, lean_object* v_firstChoiceOnly_1707_, lean_object* v_toBind_1708_, lean_object* v___f_1709_, lean_object* v___x_1710_, lean_object* v___f_1711_, lean_object* v_____do__lift_1712_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1713_; lean_object* v_res_1714_; 
v_firstChoiceOnly_boxed_1713_ = lean_unbox(v_firstChoiceOnly_1707_);
v_res_1714_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4(v_toPure_1703_, v_stx_1704_, v_inst_1705_, v_f_1706_, v_firstChoiceOnly_boxed_1713_, v_toBind_1708_, v___f_1709_, v___x_1710_, v___f_1711_, v_____do__lift_1712_);
lean_dec(v___x_1710_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(lean_object* v_inst_1715_, lean_object* v_f_1716_, uint8_t v_firstChoiceOnly_1717_, lean_object* v_stx_1718_, lean_object* v_b_1719_){
_start:
{
lean_object* v_toApplicative_1720_; lean_object* v_toBind_1721_; lean_object* v_toPure_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___f_1725_; lean_object* v___f_1726_; lean_object* v___x_1727_; lean_object* v___f_1728_; lean_object* v___x_1729_; 
v_toApplicative_1720_ = lean_ctor_get(v_inst_1715_, 0);
v_toBind_1721_ = lean_ctor_get(v_inst_1715_, 1);
lean_inc_n(v_toBind_1721_, 2);
v_toPure_1722_ = lean_ctor_get(v_toApplicative_1720_, 1);
lean_inc_n(v_toPure_1722_, 3);
v___x_1723_ = lean_box(0);
lean_inc(v_f_1716_);
lean_inc(v_stx_1718_);
v___x_1724_ = lean_apply_2(v_f_1716_, v_stx_1718_, v_b_1719_);
v___f_1725_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1725_, 0, v_toPure_1722_);
lean_inc_ref(v___f_1725_);
v___f_1726_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1726_, 0, v___f_1725_);
lean_closure_set(v___f_1726_, 1, v_toPure_1722_);
v___x_1727_ = lean_box(v_firstChoiceOnly_1717_);
v___f_1728_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_1728_, 0, v_toPure_1722_);
lean_closure_set(v___f_1728_, 1, v_stx_1718_);
lean_closure_set(v___f_1728_, 2, v_inst_1715_);
lean_closure_set(v___f_1728_, 3, v_f_1716_);
lean_closure_set(v___f_1728_, 4, v___x_1727_);
lean_closure_set(v___f_1728_, 5, v_toBind_1721_);
lean_closure_set(v___f_1728_, 6, v___f_1726_);
lean_closure_set(v___f_1728_, 7, v___x_1723_);
lean_closure_set(v___f_1728_, 8, v___f_1725_);
v___x_1729_ = lean_apply_4(v_toBind_1721_, lean_box(0), lean_box(0), v___x_1724_, v___f_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__3(lean_object* v_toPure_1730_, lean_object* v___x_1731_, lean_object* v_inst_1732_, lean_object* v_f_1733_, uint8_t v_firstChoiceOnly_1734_, lean_object* v_toBind_1735_, lean_object* v_a_1736_, lean_object* v_x_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_snd_1739_; lean_object* v___f_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v_snd_1739_ = lean_ctor_get(v___y_1738_, 1);
lean_inc_n(v_snd_1739_, 2);
lean_dec_ref(v___y_1738_);
v___f_1740_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1740_, 0, v_snd_1739_);
lean_closure_set(v___f_1740_, 1, v_toPure_1730_);
lean_closure_set(v___f_1740_, 2, v___x_1731_);
v___x_1741_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1732_, v_f_1733_, v_firstChoiceOnly_1734_, v_a_1736_, v_snd_1739_);
v___x_1742_ = lean_apply_4(v_toBind_1735_, lean_box(0), lean_box(0), v___x_1741_, v___f_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___boxed(lean_object* v_inst_1743_, lean_object* v_f_1744_, lean_object* v_firstChoiceOnly_1745_, lean_object* v_stx_1746_, lean_object* v_b_1747_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1748_; lean_object* v_res_1749_; 
v_firstChoiceOnly_boxed_1748_ = lean_unbox(v_firstChoiceOnly_1745_);
v_res_1749_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1743_, v_f_1744_, v_firstChoiceOnly_boxed_1748_, v_stx_1746_, v_b_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop(lean_object* v_m_1750_, lean_object* v_inst_1751_, lean_object* v_00_u03b2_1752_, lean_object* v_f_1753_, uint8_t v_firstChoiceOnly_1754_, lean_object* v_stx_1755_, lean_object* v_b_1756_, lean_object* v_inst_1757_){
_start:
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1751_, v_f_1753_, v_firstChoiceOnly_1754_, v_stx_1755_, v_b_1756_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___boxed(lean_object* v_m_1759_, lean_object* v_inst_1760_, lean_object* v_00_u03b2_1761_, lean_object* v_f_1762_, lean_object* v_firstChoiceOnly_1763_, lean_object* v_stx_1764_, lean_object* v_b_1765_, lean_object* v_inst_1766_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1767_; lean_object* v_res_1768_; 
v_firstChoiceOnly_boxed_1767_ = lean_unbox(v_firstChoiceOnly_1763_);
v_res_1768_ = l_Lean_Syntax_instForInTopDownOfMonad_loop(v_m_1759_, v_inst_1760_, v_00_u03b2_1761_, v_f_1762_, v_firstChoiceOnly_boxed_1767_, v_stx_1764_, v_b_1765_, v_inst_1766_);
lean_dec(v_inst_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0(lean_object* v_toPure_1769_, lean_object* v_____do__lift_1770_){
_start:
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v_____do__lift_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v_____do__lift_1770_);
v___x_1772_ = lean_apply_2(v_toPure_1769_, lean_box(0), v_a_1771_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1(lean_object* v_inst_1773_, lean_object* v_toBind_1774_, lean_object* v___f_1775_, lean_object* v_00_u03b2_1776_, lean_object* v_x_1777_, lean_object* v_init_1778_, lean_object* v_f_1779_){
_start:
{
uint8_t v_firstChoiceOnly_1780_; lean_object* v_stx_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v_firstChoiceOnly_1780_ = lean_ctor_get_uint8(v_x_1777_, sizeof(void*)*1);
v_stx_1781_ = lean_ctor_get(v_x_1777_, 0);
lean_inc(v_stx_1781_);
lean_dec_ref(v_x_1777_);
v___x_1782_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg(v_inst_1773_, v_f_1779_, v_firstChoiceOnly_1780_, v_stx_1781_, v_init_1778_);
v___x_1783_ = lean_apply_4(v_toBind_1774_, lean_box(0), lean_box(0), v___x_1782_, v___f_1775_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad___redArg(lean_object* v_inst_1784_){
_start:
{
lean_object* v_toApplicative_1785_; lean_object* v_toBind_1786_; lean_object* v_toPure_1787_; lean_object* v___f_1788_; lean_object* v___f_1789_; 
v_toApplicative_1785_ = lean_ctor_get(v_inst_1784_, 0);
v_toBind_1786_ = lean_ctor_get(v_inst_1784_, 1);
lean_inc(v_toBind_1786_);
v_toPure_1787_ = lean_ctor_get(v_toApplicative_1785_, 1);
lean_inc(v_toPure_1787_);
v___f_1788_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1788_, 0, v_toPure_1787_);
v___f_1789_ = lean_alloc_closure((void*)(l_Lean_Syntax_instForInTopDownOfMonad___redArg___lam__1), 7, 3);
lean_closure_set(v___f_1789_, 0, v_inst_1784_);
lean_closure_set(v___f_1789_, 1, v_toBind_1786_);
lean_closure_set(v___f_1789_, 2, v___f_1788_);
return v___f_1789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad(lean_object* v_m_1790_, lean_object* v_inst_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Lean_Syntax_instForInTopDownOfMonad___redArg(v_inst_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(lean_object* v_info_1794_, lean_object* v_val_1795_){
_start:
{
if (lean_obj_tag(v_info_1794_) == 0)
{
lean_object* v_leading_1796_; lean_object* v_trailing_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_leading_1796_ = lean_ctor_get(v_info_1794_, 0);
lean_inc_ref(v_leading_1796_);
v_trailing_1797_ = lean_ctor_get(v_info_1794_, 2);
lean_inc_ref(v_trailing_1797_);
lean_dec_ref_known(v_info_1794_, 4);
v___x_1798_ = lean_substring_tostring(v_leading_1796_);
v___x_1799_ = lean_string_append(v___x_1798_, v_val_1795_);
v___x_1800_ = lean_substring_tostring(v_trailing_1797_);
v___x_1801_ = lean_string_append(v___x_1799_, v___x_1800_);
lean_dec_ref(v___x_1800_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v_info_1794_);
v___x_1802_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___closed__0));
v___x_1803_ = lean_string_append(v___x_1802_, v_val_1795_);
v___x_1804_ = lean_string_append(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf___boxed(lean_object* v_info_1805_, lean_object* v_val_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1805_, v_val_1806_);
lean_dec_ref(v_val_1806_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(uint8_t v_firstChoiceOnly_1808_, lean_object* v_as_1809_, size_t v_sz_1810_, size_t v_i_1811_, lean_object* v_b_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_usize_dec_lt(v_i_1811_, v_sz_1810_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_b_1812_);
return v___x_1814_;
}
else
{
lean_object* v_snd_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1842_; 
v_snd_1815_ = lean_ctor_get(v_b_1812_, 1);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_b_1812_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; 
v_unused_1843_ = lean_ctor_get(v_b_1812_, 0);
lean_dec(v_unused_1843_);
v___x_1817_ = v_b_1812_;
v_isShared_1818_ = v_isSharedCheck_1842_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_snd_1815_);
lean_dec(v_b_1812_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1842_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_a_1819_; lean_object* v___x_1820_; 
v_a_1819_ = lean_array_uget_borrowed(v_as_1809_, v_i_1811_);
lean_inc(v_snd_1815_);
lean_inc(v_a_1819_);
v___x_1820_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_1808_, v_a_1819_, v_snd_1815_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v___x_1821_; 
lean_del_object(v___x_1817_);
lean_dec(v_snd_1815_);
v___x_1821_ = lean_box(0);
return v___x_1821_;
}
else
{
lean_object* v_val_1822_; 
v_val_1822_ = lean_ctor_get(v___x_1820_, 0);
lean_inc(v_val_1822_);
if (lean_obj_tag(v_val_1822_) == 0)
{
lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1832_; 
v_isSharedCheck_1832_ = !lean_is_exclusive(v_val_1822_);
if (v_isSharedCheck_1832_ == 0)
{
lean_object* v_unused_1833_; 
v_unused_1833_ = lean_ctor_get(v_val_1822_, 0);
lean_dec(v_unused_1833_);
v___x_1824_ = v_val_1822_;
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
else
{
lean_dec(v_val_1822_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1832_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1820_);
v___x_1827_ = v___x_1817_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_snd_1815_);
v___x_1827_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
lean_object* v___x_1829_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 1);
lean_ctor_set(v___x_1824_, 0, v___x_1827_);
v___x_1829_ = v___x_1824_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v___x_1837_; 
lean_dec_ref_known(v___x_1820_, 1);
lean_dec(v_snd_1815_);
v_a_1834_ = lean_ctor_get(v_val_1822_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v_val_1822_, 1);
v___x_1835_ = lean_box(0);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v_a_1834_);
lean_ctor_set(v___x_1817_, 0, v___x_1835_);
v___x_1837_ = v___x_1817_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_a_1834_);
v___x_1837_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
size_t v___x_1838_; size_t v___x_1839_; 
v___x_1838_ = ((size_t)1ULL);
v___x_1839_ = lean_usize_add(v_i_1811_, v___x_1838_);
v_i_1811_ = v___x_1839_;
v_b_1812_ = v___x_1837_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(lean_object* v_val_1844_, lean_object* v_a_1845_, lean_object* v_b_1846_){
_start:
{
lean_object* v_array_1847_; lean_object* v_start_1848_; lean_object* v_stop_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1868_; 
v_array_1847_ = lean_ctor_get(v_a_1845_, 0);
v_start_1848_ = lean_ctor_get(v_a_1845_, 1);
v_stop_1849_ = lean_ctor_get(v_a_1845_, 2);
v_isSharedCheck_1868_ = !lean_is_exclusive(v_a_1845_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1851_ = v_a_1845_;
v_isShared_1852_ = v_isSharedCheck_1868_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_stop_1849_);
lean_inc(v_start_1848_);
lean_inc(v_array_1847_);
lean_dec(v_a_1845_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1868_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
uint8_t v___x_1853_; 
v___x_1853_ = lean_nat_dec_lt(v_start_1848_, v_stop_1849_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_del_object(v___x_1851_);
lean_dec(v_stop_1849_);
lean_dec(v_start_1848_);
lean_dec_ref(v_array_1847_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_b_1846_);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_array_fget_borrowed(v_array_1847_, v_start_1848_);
lean_inc(v___x_1855_);
v___x_1856_ = l_Lean_Syntax_reprint(v___x_1855_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; 
lean_del_object(v___x_1851_);
lean_dec(v_stop_1849_);
lean_dec(v_start_1848_);
lean_dec_ref(v_array_1847_);
v___x_1857_ = lean_box(0);
return v___x_1857_;
}
else
{
lean_object* v_val_1858_; uint8_t v___x_1859_; 
v_val_1858_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_val_1858_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1859_ = lean_string_dec_eq(v_val_1844_, v_val_1858_);
lean_dec(v_val_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_del_object(v___x_1851_);
lean_dec(v_stop_1849_);
lean_dec(v_start_1848_);
lean_dec_ref(v_array_1847_);
v___x_1860_ = lean_box(0);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_unsigned_to_nat(1u);
v___x_1863_ = lean_nat_add(v_start_1848_, v___x_1862_);
lean_dec(v_start_1848_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v___x_1863_);
v___x_1865_ = v___x_1851_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_array_1847_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1867_, 2, v_stop_1849_);
v___x_1865_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v_a_1845_ = v___x_1865_;
v_b_1846_ = v___x_1861_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(uint8_t v_firstChoiceOnly_1869_, lean_object* v_stx_1870_, lean_object* v_b_1871_){
_start:
{
lean_object* v_b_1873_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___x_1887_; lean_object* v_a_1889_; 
v___x_1887_ = lean_box(0);
switch(lean_obj_tag(v_stx_1870_))
{
case 2:
{
lean_object* v_info_1898_; lean_object* v_val_1899_; lean_object* v___x_1900_; lean_object* v_s_1901_; 
v_info_1898_ = lean_ctor_get(v_stx_1870_, 0);
v_val_1899_ = lean_ctor_get(v_stx_1870_, 1);
lean_inc(v_info_1898_);
v___x_1900_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1898_, v_val_1899_);
v_s_1901_ = lean_string_append(v_b_1871_, v___x_1900_);
lean_dec_ref(v___x_1900_);
v_a_1889_ = v_s_1901_;
goto v___jp_1888_;
}
case 3:
{
lean_object* v_rawVal_1902_; lean_object* v_info_1903_; lean_object* v_str_1904_; lean_object* v_startPos_1905_; lean_object* v_stopPos_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v_s_1909_; 
v_rawVal_1902_ = lean_ctor_get(v_stx_1870_, 1);
v_info_1903_ = lean_ctor_get(v_stx_1870_, 0);
v_str_1904_ = lean_ctor_get(v_rawVal_1902_, 0);
v_startPos_1905_ = lean_ctor_get(v_rawVal_1902_, 1);
v_stopPos_1906_ = lean_ctor_get(v_rawVal_1902_, 2);
v___x_1907_ = lean_string_utf8_extract(v_str_1904_, v_startPos_1905_, v_stopPos_1906_);
lean_inc(v_info_1903_);
v___x_1908_ = l___private_Lean_Syntax_0__Lean_Syntax_reprint_reprintLeaf(v_info_1903_, v___x_1907_);
lean_dec_ref(v___x_1907_);
v_s_1909_ = lean_string_append(v_b_1871_, v___x_1908_);
lean_dec_ref(v___x_1908_);
v_a_1889_ = v_s_1909_;
goto v___jp_1888_;
}
case 1:
{
lean_object* v_kind_1910_; lean_object* v_args_1911_; lean_object* v___x_1912_; uint8_t v___x_1913_; 
v_kind_1910_ = lean_ctor_get(v_stx_1870_, 1);
v_args_1911_ = lean_ctor_get(v_stx_1870_, 2);
v___x_1912_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1913_ = lean_name_eq(v_kind_1910_, v___x_1912_);
if (v___x_1913_ == 0)
{
v_a_1889_ = v_b_1871_;
goto v___jp_1888_;
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_get_borrowed(v___x_1887_, v_args_1911_, v___x_1914_);
lean_inc(v___x_1915_);
v___x_1916_ = l_Lean_Syntax_reprint(v___x_1915_);
if (lean_obj_tag(v___x_1916_) == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref_known(v_stx_1870_, 3);
lean_dec_ref(v_b_1871_);
v___x_1917_ = lean_box(0);
return v___x_1917_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_val_1918_ = lean_ctor_get(v___x_1916_, 0);
lean_inc(v_val_1918_);
lean_dec_ref_known(v___x_1916_, 1);
v___x_1919_ = lean_unsigned_to_nat(1u);
v___x_1920_ = lean_array_get_size(v_args_1911_);
lean_inc_ref(v_args_1911_);
v___x_1921_ = l_Array_toSubarray___redArg(v_args_1911_, v___x_1919_, v___x_1920_);
v___x_1922_ = lean_box(0);
v___x_1923_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1918_, v___x_1921_, v___x_1922_);
lean_dec(v_val_1918_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v___x_1924_; 
lean_dec_ref_known(v_stx_1870_, 3);
lean_dec_ref(v_b_1871_);
v___x_1924_ = lean_box(0);
return v___x_1924_;
}
else
{
lean_dec_ref_known(v___x_1923_, 1);
v_a_1889_ = v_b_1871_;
goto v___jp_1888_;
}
}
}
}
default: 
{
v_a_1889_ = v_b_1871_;
goto v___jp_1888_;
}
}
v___jp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v_b_1873_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
v___jp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; size_t v_sz_1881_; size_t v___x_1882_; lean_object* v___x_1883_; 
v___x_1879_ = lean_box(0);
v___x_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v___y_1878_);
v_sz_1881_ = lean_array_size(v___y_1877_);
v___x_1882_ = ((size_t)0ULL);
v___x_1883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_1869_, v___y_1877_, v_sz_1881_, v___x_1882_, v___x_1880_);
lean_dec_ref(v___y_1877_);
if (lean_obj_tag(v___x_1883_) == 0)
{
return v___x_1879_;
}
else
{
lean_object* v_val_1884_; lean_object* v_fst_1885_; 
v_val_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_val_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v_fst_1885_ = lean_ctor_get(v_val_1884_, 0);
if (lean_obj_tag(v_fst_1885_) == 0)
{
lean_object* v_snd_1886_; 
v_snd_1886_ = lean_ctor_get(v_val_1884_, 1);
lean_inc(v_snd_1886_);
lean_dec(v_val_1884_);
v_b_1873_ = v_snd_1886_;
goto v___jp_1872_;
}
else
{
lean_inc_ref(v_fst_1885_);
lean_dec(v_val_1884_);
return v_fst_1885_;
}
}
}
v___jp_1888_:
{
if (lean_obj_tag(v_stx_1870_) == 1)
{
if (v_firstChoiceOnly_1869_ == 0)
{
lean_object* v_args_1890_; 
v_args_1890_ = lean_ctor_get(v_stx_1870_, 2);
lean_inc_ref(v_args_1890_);
lean_dec_ref_known(v_stx_1870_, 3);
v___y_1877_ = v_args_1890_;
v___y_1878_ = v_a_1889_;
goto v___jp_1876_;
}
else
{
lean_object* v_kind_1891_; lean_object* v_args_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_kind_1891_ = lean_ctor_get(v_stx_1870_, 1);
lean_inc(v_kind_1891_);
v_args_1892_ = lean_ctor_get(v_stx_1870_, 2);
lean_inc_ref(v_args_1892_);
lean_dec_ref_known(v_stx_1870_, 3);
v___x_1893_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1894_ = lean_name_eq(v_kind_1891_, v___x_1893_);
lean_dec(v_kind_1891_);
if (v___x_1894_ == 0)
{
v___y_1877_ = v_args_1892_;
v___y_1878_ = v_a_1889_;
goto v___jp_1876_;
}
else
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_array_get(v___x_1887_, v_args_1892_, v___x_1895_);
lean_dec_ref(v_args_1892_);
v_stx_1870_ = v___x_1896_;
v_b_1871_ = v_a_1889_;
goto _start;
}
}
}
else
{
lean_dec(v_stx_1870_);
v_b_1873_ = v_a_1889_;
goto v___jp_1872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_reprint(lean_object* v_stx_1925_){
_start:
{
lean_object* v_s_1926_; uint8_t v___x_1927_; lean_object* v___x_1928_; 
v_s_1926_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
v___x_1927_ = 1;
v___x_1928_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v___x_1927_, v_stx_1925_, v_s_1926_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1929_; 
v___x_1929_ = lean_box(0);
return v___x_1929_;
}
else
{
lean_object* v_val_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1938_; 
v_val_1930_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1932_ = v___x_1928_;
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_val_1930_);
lean_dec(v___x_1928_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1938_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v_a_1934_; lean_object* v___x_1936_; 
v_a_1934_ = lean_ctor_get(v_val_1930_, 0);
lean_inc(v_a_1934_);
lean_dec(v_val_1930_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v_a_1934_);
v___x_1936_ = v___x_1932_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg___boxed(lean_object* v_val_1939_, lean_object* v_a_1940_, lean_object* v_b_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1939_, v_a_1940_, v_b_1941_);
lean_dec_ref(v_val_1939_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1___boxed(lean_object* v_firstChoiceOnly_1943_, lean_object* v_as_1944_, lean_object* v_sz_1945_, lean_object* v_i_1946_, lean_object* v_b_1947_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1948_; size_t v_sz_boxed_1949_; size_t v_i_boxed_1950_; lean_object* v_res_1951_; 
v_firstChoiceOnly_boxed_1948_ = lean_unbox(v_firstChoiceOnly_1943_);
v_sz_boxed_1949_ = lean_unbox_usize(v_sz_1945_);
lean_dec(v_sz_1945_);
v_i_boxed_1950_ = lean_unbox_usize(v_i_1946_);
lean_dec(v_i_1946_);
v_res_1951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1_spec__1(v_firstChoiceOnly_boxed_1948_, v_as_1944_, v_sz_boxed_1949_, v_i_boxed_1950_, v_b_1947_);
lean_dec_ref(v_as_1944_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1___boxed(lean_object* v_firstChoiceOnly_1952_, lean_object* v_stx_1953_, lean_object* v_b_1954_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_1955_; lean_object* v_res_1956_; 
v_firstChoiceOnly_boxed_1955_ = lean_unbox(v_firstChoiceOnly_1952_);
v_res_1956_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_reprint_spec__1(v_firstChoiceOnly_boxed_1955_, v_stx_1953_, v_b_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(lean_object* v_val_1957_, lean_object* v_inst_1958_, lean_object* v_R_1959_, lean_object* v_a_1960_, lean_object* v_b_1961_, lean_object* v_c_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___redArg(v_val_1957_, v_a_1960_, v_b_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0___boxed(lean_object* v_val_1964_, lean_object* v_inst_1965_, lean_object* v_R_1966_, lean_object* v_a_1967_, lean_object* v_b_1968_, lean_object* v_c_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Syntax_reprint_spec__0(v_val_1964_, v_inst_1965_, v_R_1966_, v_a_1967_, v_b_1968_, v_c_1969_);
lean_dec_ref(v_val_1964_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(uint8_t v_firstChoiceOnly_1979_, lean_object* v_stx_1980_){
_start:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_box(0);
v___x_1982_ = l_Lean_Syntax_isMissing(v_stx_1980_);
if (v___x_1982_ == 0)
{
if (lean_obj_tag(v_stx_1980_) == 1)
{
lean_object* v_kind_1983_; lean_object* v_args_1984_; 
v_kind_1983_ = lean_ctor_get(v_stx_1980_, 1);
v_args_1984_ = lean_ctor_get(v_stx_1980_, 2);
if (v_firstChoiceOnly_1979_ == 0)
{
goto v___jp_1985_;
}
else
{
lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1994_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
v___x_1995_ = lean_name_eq(v_kind_1983_, v___x_1994_);
if (v___x_1995_ == 0)
{
goto v___jp_1985_;
}
else
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = lean_array_get_borrowed(v___x_1996_, v_args_1984_, v___x_1997_);
v_stx_1980_ = v___x_1998_;
goto _start;
}
}
v___jp_1985_:
{
lean_object* v___x_1986_; size_t v_sz_1987_; size_t v___x_1988_; lean_object* v___x_1989_; lean_object* v_fst_1990_; 
v___x_1986_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__1));
v_sz_1987_ = lean_array_size(v_args_1984_);
v___x_1988_ = ((size_t)0ULL);
v___x_1989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_1979_, v_args_1984_, v_sz_1987_, v___x_1988_, v___x_1986_);
v_fst_1990_ = lean_ctor_get(v___x_1989_, 0);
if (lean_obj_tag(v_fst_1990_) == 0)
{
lean_object* v_snd_1991_; lean_object* v___x_1992_; 
v_snd_1991_ = lean_ctor_get(v___x_1989_, 1);
lean_inc(v_snd_1991_);
lean_dec_ref(v___x_1989_);
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_snd_1991_);
return v___x_1992_;
}
else
{
lean_object* v_val_1993_; 
lean_inc_ref(v_fst_1990_);
lean_dec_ref(v___x_1989_);
v_val_1993_ = lean_ctor_get(v_fst_1990_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v_fst_1990_, 1);
return v_val_1993_;
}
}
}
else
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___closed__2));
return v___x_2000_;
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2001_ = lean_box(v___x_1982_);
v___x_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
lean_ctor_set(v___x_2003_, 1, v___x_1981_);
v___x_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
return v___x_2004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(uint8_t v_firstChoiceOnly_2005_, lean_object* v_as_2006_, size_t v_sz_2007_, size_t v_i_2008_, lean_object* v_b_2009_){
_start:
{
uint8_t v___x_2010_; 
v___x_2010_ = lean_usize_dec_lt(v_i_2008_, v_sz_2007_);
if (v___x_2010_ == 0)
{
return v_b_2009_;
}
else
{
lean_object* v_snd_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2029_; 
v_snd_2011_ = lean_ctor_get(v_b_2009_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_b_2009_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v_b_2009_, 0);
lean_dec(v_unused_2030_);
v___x_2013_ = v_b_2009_;
v_isShared_2014_ = v_isSharedCheck_2029_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_snd_2011_);
lean_dec(v_b_2009_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2029_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_a_2015_; lean_object* v___x_2016_; 
v_a_2015_ = lean_array_uget_borrowed(v_as_2006_, v_i_2008_);
v___x_2016_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_2005_, v_a_2015_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___x_2016_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 0, v___x_2017_);
v___x_2019_ = v___x_2013_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_snd_2011_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_dec(v_snd_2011_);
v_a_2021_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2022_ = lean_box(0);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v_a_2021_);
lean_ctor_set(v___x_2013_, 0, v___x_2022_);
v___x_2024_ = v___x_2013_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2022_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_a_2021_);
v___x_2024_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
size_t v___x_2025_; size_t v___x_2026_; 
v___x_2025_ = ((size_t)1ULL);
v___x_2026_ = lean_usize_add(v_i_2008_, v___x_2025_);
v_i_2008_ = v___x_2026_;
v_b_2009_ = v___x_2024_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0___boxed(lean_object* v_firstChoiceOnly_2031_, lean_object* v_as_2032_, lean_object* v_sz_2033_, lean_object* v_i_2034_, lean_object* v_b_2035_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2036_; size_t v_sz_boxed_2037_; size_t v_i_boxed_2038_; lean_object* v_res_2039_; 
v_firstChoiceOnly_boxed_2036_ = lean_unbox(v_firstChoiceOnly_2031_);
v_sz_boxed_2037_ = lean_unbox_usize(v_sz_2033_);
lean_dec(v_sz_2033_);
v_i_boxed_2038_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_res_2039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0_spec__0(v_firstChoiceOnly_boxed_2036_, v_as_2032_, v_sz_boxed_2037_, v_i_boxed_2038_, v_b_2035_);
lean_dec_ref(v_as_2032_);
return v_res_2039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg___boxed(lean_object* v_firstChoiceOnly_2040_, lean_object* v_stx_2041_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2042_; lean_object* v_res_2043_; 
v_firstChoiceOnly_boxed_2042_ = lean_unbox(v_firstChoiceOnly_2040_);
v_res_2043_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_boxed_2042_, v_stx_2041_);
lean_dec(v_stx_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_hasMissing(lean_object* v_stx_2044_){
_start:
{
uint8_t v___x_2045_; lean_object* v___y_2047_; lean_object* v___x_2051_; lean_object* v_a_2052_; 
v___x_2045_ = 0;
v___x_2051_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v___x_2045_, v_stx_2044_);
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref(v___x_2051_);
v___y_2047_ = v_a_2052_;
goto v___jp_2046_;
v___jp_2046_:
{
lean_object* v_fst_2048_; 
v_fst_2048_ = lean_ctor_get(v___y_2047_, 0);
lean_inc(v_fst_2048_);
lean_dec_ref(v___y_2047_);
if (lean_obj_tag(v_fst_2048_) == 0)
{
return v___x_2045_;
}
else
{
lean_object* v_val_2049_; uint8_t v___x_2050_; 
v_val_2049_ = lean_ctor_get(v_fst_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v_fst_2048_, 1);
v___x_2050_ = lean_unbox(v_val_2049_);
lean_dec(v_val_2049_);
return v___x_2050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_hasMissing___boxed(lean_object* v_stx_2053_){
_start:
{
uint8_t v_res_2054_; lean_object* v_r_2055_; 
v_res_2054_ = l_Lean_Syntax_hasMissing(v_stx_2053_);
lean_dec(v_stx_2053_);
v_r_2055_ = lean_box(v_res_2054_);
return v_r_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(uint8_t v_firstChoiceOnly_2056_, lean_object* v_stx_2057_, lean_object* v_b_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___redArg(v_firstChoiceOnly_2056_, v_stx_2057_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0___boxed(lean_object* v_firstChoiceOnly_2060_, lean_object* v_stx_2061_, lean_object* v_b_2062_){
_start:
{
uint8_t v_firstChoiceOnly_boxed_2063_; lean_object* v_res_2064_; 
v_firstChoiceOnly_boxed_2063_ = lean_unbox(v_firstChoiceOnly_2060_);
v_res_2064_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Syntax_hasMissing_spec__0(v_firstChoiceOnly_boxed_2063_, v_stx_2061_, v_b_2062_);
lean_dec_ref(v_b_2062_);
lean_dec(v_stx_2061_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f(lean_object* v_stx_2065_, uint8_t v_canonicalOnly_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Syntax_getPos_x3f(v_stx_2065_, v_canonicalOnly_2066_);
if (lean_obj_tag(v___x_2067_) == 1)
{
lean_object* v_val_2068_; lean_object* v___x_2069_; 
v_val_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v___x_2067_, 1);
v___x_2069_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2065_, v_canonicalOnly_2066_);
if (lean_obj_tag(v___x_2069_) == 1)
{
lean_object* v_val_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_val_2070_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v___x_2069_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_val_2070_);
lean_dec(v___x_2069_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v_val_2068_);
lean_ctor_set(v___x_2074_, 1, v_val_2070_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
else
{
lean_object* v___x_2079_; 
lean_dec(v___x_2069_);
lean_dec(v_val_2068_);
v___x_2079_ = lean_box(0);
return v___x_2079_;
}
}
else
{
lean_object* v___x_2080_; 
lean_dec(v___x_2067_);
v___x_2080_ = lean_box(0);
return v___x_2080_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRange_x3f___boxed(lean_object* v_stx_2081_, lean_object* v_canonicalOnly_2082_){
_start:
{
uint8_t v_canonicalOnly_boxed_2083_; lean_object* v_res_2084_; 
v_canonicalOnly_boxed_2083_ = lean_unbox(v_canonicalOnly_2082_);
v_res_2084_ = l_Lean_Syntax_getRange_x3f(v_stx_2081_, v_canonicalOnly_boxed_2083_);
lean_dec(v_stx_2081_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object* v_stx_2085_, uint8_t v_canonicalOnly_2086_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Syntax_getPos_x3f(v_stx_2085_, v_canonicalOnly_2086_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_box(0);
return v___x_2088_;
}
else
{
lean_object* v_val_2089_; lean_object* v___x_2090_; 
v_val_2089_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_val_2089_);
lean_dec_ref_known(v___x_2087_, 1);
v___x_2090_ = l_Lean_Syntax_getTrailingTailPos_x3f(v_stx_2085_, v_canonicalOnly_2086_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v___x_2091_; 
lean_dec(v_val_2089_);
v___x_2091_ = lean_box(0);
return v___x_2091_;
}
else
{
lean_object* v_val_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2100_; 
v_val_2092_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2094_ = v___x_2090_;
v_isShared_2095_ = v_isSharedCheck_2100_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_val_2092_);
lean_dec(v___x_2090_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2100_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v_val_2089_);
lean_ctor_set(v___x_2096_, 1, v_val_2092_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2096_);
v___x_2098_ = v___x_2094_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f___boxed(lean_object* v_stx_2101_, lean_object* v_canonicalOnly_2102_){
_start:
{
uint8_t v_canonicalOnly_boxed_2103_; lean_object* v_res_2104_; 
v_canonicalOnly_boxed_2103_ = lean_unbox(v_canonicalOnly_2102_);
v_res_2104_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_2101_, v_canonicalOnly_boxed_2103_);
lean_dec(v_stx_2101_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange(lean_object* v_range_2105_, uint8_t v_canonical_2106_){
_start:
{
lean_object* v_start_2107_; lean_object* v_stop_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2117_; 
v_start_2107_ = lean_ctor_get(v_range_2105_, 0);
v_stop_2108_ = lean_ctor_get(v_range_2105_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_range_2105_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2110_ = v_range_2105_;
v_isShared_2111_ = v_isSharedCheck_2117_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_stop_2108_);
lean_inc(v_start_2107_);
lean_dec(v_range_2105_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2117_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2112_ = lean_alloc_ctor(1, 2, 1);
lean_ctor_set(v___x_2112_, 0, v_start_2107_);
lean_ctor_set(v___x_2112_, 1, v_stop_2108_);
lean_ctor_set_uint8(v___x_2112_, sizeof(void*)*2, v_canonical_2106_);
v___x_2113_ = ((lean_object*)(l_Lean_Syntax_getAtomVal___closed__0));
if (v_isShared_2111_ == 0)
{
lean_ctor_set_tag(v___x_2110_, 2);
lean_ctor_set(v___x_2110_, 1, v___x_2113_);
lean_ctor_set(v___x_2110_, 0, v___x_2112_);
v___x_2115_ = v___x_2110_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_ofRange___boxed(lean_object* v_range_2118_, lean_object* v_canonical_2119_){
_start:
{
uint8_t v_canonical_boxed_2120_; lean_object* v_res_2121_; 
v_canonical_boxed_2120_ = lean_unbox(v_canonical_2119_);
v_res_2121_ = l_Lean_Syntax_ofRange(v_range_2118_, v_canonical_boxed_2120_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_fromSyntax(lean_object* v_stx_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l_Lean_Syntax_Traverser_fromSyntax___closed__0));
v___x_2126_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2126_, 0, v_stx_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
lean_ctor_set(v___x_2126_, 2, v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_setCur(lean_object* v_t_2127_, lean_object* v_stx_2128_){
_start:
{
lean_object* v_parents_2129_; lean_object* v_idxs_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_parents_2129_ = lean_ctor_get(v_t_2127_, 1);
v_idxs_2130_ = lean_ctor_get(v_t_2127_, 2);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_t_2127_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v_t_2127_, 0);
lean_dec(v_unused_2138_);
v___x_2132_ = v_t_2127_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_idxs_2130_);
lean_inc(v_parents_2129_);
lean_dec(v_t_2127_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v_stx_2128_);
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_stx_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_parents_2129_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_idxs_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_down(lean_object* v_t_2139_, lean_object* v_idx_2140_){
_start:
{
lean_object* v_cur_2141_; lean_object* v_parents_2142_; lean_object* v_idxs_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2163_; 
v_cur_2141_ = lean_ctor_get(v_t_2139_, 0);
v_parents_2142_ = lean_ctor_get(v_t_2139_, 1);
v_idxs_2143_ = lean_ctor_get(v_t_2139_, 2);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_t_2139_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2145_ = v_t_2139_;
v_isShared_2146_ = v_isSharedCheck_2163_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_idxs_2143_);
lean_inc(v_parents_2142_);
lean_inc(v_cur_2141_);
lean_dec(v_t_2139_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2163_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = l_Lean_Syntax_getNumArgs(v_cur_2141_);
v___x_2148_ = lean_nat_dec_lt(v_idx_2140_, v___x_2147_);
lean_dec(v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2149_ = lean_box(0);
v___x_2150_ = lean_array_push(v_parents_2142_, v_cur_2141_);
v___x_2151_ = lean_array_push(v_idxs_2143_, v_idx_2140_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 2, v___x_2151_);
lean_ctor_set(v___x_2145_, 1, v___x_2150_);
lean_ctor_set(v___x_2145_, 0, v___x_2149_);
v___x_2153_ = v___x_2145_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v___x_2151_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2161_; 
v___x_2155_ = l_Lean_Syntax_getArg(v_cur_2141_, v_idx_2140_);
v___x_2156_ = lean_box(0);
v___x_2157_ = l_Lean_Syntax_setArg(v_cur_2141_, v_idx_2140_, v___x_2156_);
v___x_2158_ = lean_array_push(v_parents_2142_, v___x_2157_);
v___x_2159_ = lean_array_push(v_idxs_2143_, v_idx_2140_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 2, v___x_2159_);
lean_ctor_set(v___x_2145_, 1, v___x_2158_);
lean_ctor_set(v___x_2145_, 0, v___x_2155_);
v___x_2161_ = v___x_2145_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2155_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v___x_2159_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_up(lean_object* v_t_2164_){
_start:
{
lean_object* v_cur_2165_; lean_object* v_parents_2166_; lean_object* v_idxs_2167_; lean_object* v___y_2169_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; 
v_cur_2165_ = lean_ctor_get(v_t_2164_, 0);
v_parents_2166_ = lean_ctor_get(v_t_2164_, 1);
v_idxs_2167_ = lean_ctor_get(v_t_2164_, 2);
v___x_2173_ = lean_unsigned_to_nat(0u);
v___x_2174_ = lean_array_get_size(v_parents_2166_);
v___x_2175_ = lean_nat_dec_lt(v___x_2173_, v___x_2174_);
if (v___x_2175_ == 0)
{
return v_t_2164_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
lean_inc_ref(v_idxs_2167_);
lean_inc_ref(v_parents_2166_);
lean_inc(v_cur_2165_);
lean_dec_ref(v_t_2164_);
v___x_2176_ = lean_box(0);
v___x_2177_ = lean_array_get_size(v_idxs_2167_);
v___x_2178_ = lean_unsigned_to_nat(1u);
v___x_2179_ = lean_nat_sub(v___x_2177_, v___x_2178_);
v___x_2180_ = lean_array_get_borrowed(v___x_2173_, v_idxs_2167_, v___x_2179_);
lean_dec(v___x_2179_);
v___x_2181_ = lean_nat_sub(v___x_2174_, v___x_2178_);
v___x_2182_ = lean_array_get_borrowed(v___x_2176_, v_parents_2166_, v___x_2181_);
lean_dec(v___x_2181_);
v___x_2183_ = l_Lean_Syntax_getNumArgs(v___x_2182_);
v___x_2184_ = lean_nat_dec_lt(v___x_2180_, v___x_2183_);
lean_dec(v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec(v_cur_2165_);
lean_inc(v___x_2182_);
v___y_2169_ = v___x_2182_;
goto v___jp_2168_;
}
else
{
lean_object* v___x_2185_; 
lean_inc(v___x_2182_);
v___x_2185_ = l_Lean_Syntax_setArg(v___x_2182_, v___x_2180_, v_cur_2165_);
v___y_2169_ = v___x_2185_;
goto v___jp_2168_;
}
}
v___jp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_array_pop(v_parents_2166_);
v___x_2171_ = lean_array_pop(v_idxs_2167_);
v___x_2172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2172_, 0, v___y_2169_);
lean_ctor_set(v___x_2172_, 1, v___x_2170_);
lean_ctor_set(v___x_2172_, 2, v___x_2171_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_left(lean_object* v_t_2186_){
_start:
{
lean_object* v_parents_2187_; lean_object* v_idxs_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_parents_2187_ = lean_ctor_get(v_t_2186_, 1);
v_idxs_2188_ = lean_ctor_get(v_t_2186_, 2);
v___x_2189_ = lean_unsigned_to_nat(0u);
v___x_2190_ = lean_array_get_size(v_parents_2187_);
v___x_2191_ = lean_nat_dec_lt(v___x_2189_, v___x_2190_);
if (v___x_2191_ == 0)
{
return v_t_2186_;
}
else
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_inc_ref(v_idxs_2188_);
v___x_2192_ = l_Lean_Syntax_Traverser_up(v_t_2186_);
v___x_2193_ = lean_array_get_size(v_idxs_2188_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_sub(v___x_2193_, v___x_2194_);
v___x_2196_ = lean_array_get(v___x_2189_, v_idxs_2188_, v___x_2195_);
lean_dec(v___x_2195_);
lean_dec_ref(v_idxs_2188_);
v___x_2197_ = lean_nat_sub(v___x_2196_, v___x_2194_);
lean_dec(v___x_2196_);
v___x_2198_ = l_Lean_Syntax_Traverser_down(v___x_2192_, v___x_2197_);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Traverser_right(lean_object* v_t_2199_){
_start:
{
lean_object* v_parents_2200_; lean_object* v_idxs_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_parents_2200_ = lean_ctor_get(v_t_2199_, 1);
v_idxs_2201_ = lean_ctor_get(v_t_2199_, 2);
v___x_2202_ = lean_unsigned_to_nat(0u);
v___x_2203_ = lean_array_get_size(v_parents_2200_);
v___x_2204_ = lean_nat_dec_lt(v___x_2202_, v___x_2203_);
if (v___x_2204_ == 0)
{
return v_t_2199_;
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_inc_ref(v_idxs_2201_);
v___x_2205_ = l_Lean_Syntax_Traverser_up(v_t_2199_);
v___x_2206_ = lean_array_get_size(v_idxs_2201_);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_sub(v___x_2206_, v___x_2207_);
v___x_2209_ = lean_array_get(v___x_2202_, v_idxs_2201_, v___x_2208_);
lean_dec(v___x_2208_);
lean_dec_ref(v_idxs_2201_);
v___x_2210_ = lean_nat_add(v___x_2209_, v___x_2207_);
lean_dec(v___x_2209_);
v___x_2211_ = l_Lean_Syntax_Traverser_down(v___x_2205_, v___x_2210_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(lean_object* v_self_2212_){
_start:
{
lean_object* v_cur_2213_; 
v_cur_2213_ = lean_ctor_get(v_self_2212_, 0);
lean_inc(v_cur_2213_);
return v_cur_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0___boxed(lean_object* v_self_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_Syntax_MonadTraverser_getCur___redArg___lam__0(v_self_2214_);
lean_dec_ref(v_self_2214_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur___redArg(lean_object* v_inst_2217_, lean_object* v_t_2218_){
_start:
{
lean_object* v_toApplicative_2219_; lean_object* v_toFunctor_2220_; lean_object* v_map_2221_; lean_object* v_get_2222_; lean_object* v___f_2223_; lean_object* v___x_2224_; 
v_toApplicative_2219_ = lean_ctor_get(v_inst_2217_, 0);
lean_inc_ref(v_toApplicative_2219_);
lean_dec_ref(v_inst_2217_);
v_toFunctor_2220_ = lean_ctor_get(v_toApplicative_2219_, 0);
lean_inc_ref(v_toFunctor_2220_);
lean_dec_ref(v_toApplicative_2219_);
v_map_2221_ = lean_ctor_get(v_toFunctor_2220_, 0);
lean_inc(v_map_2221_);
lean_dec_ref(v_toFunctor_2220_);
v_get_2222_ = lean_ctor_get(v_t_2218_, 0);
lean_inc(v_get_2222_);
lean_dec_ref(v_t_2218_);
v___f_2223_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_getCur___redArg___closed__0));
v___x_2224_ = lean_apply_4(v_map_2221_, lean_box(0), lean_box(0), v___f_2223_, v_get_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getCur(lean_object* v_m_2225_, lean_object* v_inst_2226_, lean_object* v_t_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_Syntax_MonadTraverser_getCur___redArg(v_inst_2226_, v_t_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0(lean_object* v_stx_2229_, lean_object* v_s_2230_){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = l_Lean_Syntax_Traverser_setCur(v_s_2230_, v_stx_2229_);
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2231_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur___redArg(lean_object* v_t_2234_, lean_object* v_stx_2235_){
_start:
{
lean_object* v_modifyGet_2236_; lean_object* v___f_2237_; lean_object* v___x_2238_; 
v_modifyGet_2236_ = lean_ctor_get(v_t_2234_, 2);
lean_inc(v_modifyGet_2236_);
lean_dec_ref(v_t_2234_);
v___f_2237_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_setCur___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2237_, 0, v_stx_2235_);
v___x_2238_ = lean_apply_2(v_modifyGet_2236_, lean_box(0), v___f_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_setCur(lean_object* v_m_2239_, lean_object* v_t_2240_, lean_object* v_stx_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Syntax_MonadTraverser_setCur___redArg(v_t_2240_, v_stx_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0(lean_object* v_idx_2243_, lean_object* v_s_2244_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = l_Lean_Syntax_Traverser_down(v_s_2244_, v_idx_2243_);
v___x_2247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2245_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown___redArg(lean_object* v_t_2248_, lean_object* v_idx_2249_){
_start:
{
lean_object* v_modifyGet_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; 
v_modifyGet_2250_ = lean_ctor_get(v_t_2248_, 2);
lean_inc(v_modifyGet_2250_);
lean_dec_ref(v_t_2248_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_goDown___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2251_, 0, v_idx_2249_);
v___x_2252_ = lean_apply_2(v_modifyGet_2250_, lean_box(0), v___f_2251_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goDown(lean_object* v_m_2253_, lean_object* v_t_2254_, lean_object* v_idx_2255_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Syntax_MonadTraverser_goDown___redArg(v_t_2254_, v_idx_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg___lam__0(lean_object* v_s_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2258_ = lean_box(0);
v___x_2259_ = l_Lean_Syntax_Traverser_up(v_s_2257_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp___redArg(lean_object* v_t_2262_){
_start:
{
lean_object* v_modifyGet_2263_; lean_object* v___f_2264_; lean_object* v___x_2265_; 
v_modifyGet_2263_ = lean_ctor_get(v_t_2262_, 2);
lean_inc(v_modifyGet_2263_);
lean_dec_ref(v_t_2262_);
v___f_2264_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goUp___redArg___closed__0));
v___x_2265_ = lean_apply_2(v_modifyGet_2263_, lean_box(0), v___f_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goUp(lean_object* v_m_2266_, lean_object* v_t_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Syntax_MonadTraverser_goUp___redArg(v_t_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg___lam__0(lean_object* v_s_2269_){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2270_ = lean_box(0);
v___x_2271_ = l_Lean_Syntax_Traverser_left(v_s_2269_);
v___x_2272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft___redArg(lean_object* v_t_2274_){
_start:
{
lean_object* v_modifyGet_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; 
v_modifyGet_2275_ = lean_ctor_get(v_t_2274_, 2);
lean_inc(v_modifyGet_2275_);
lean_dec_ref(v_t_2274_);
v___f_2276_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goLeft___redArg___closed__0));
v___x_2277_ = lean_apply_2(v_modifyGet_2275_, lean_box(0), v___f_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goLeft(lean_object* v_m_2278_, lean_object* v_t_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Syntax_MonadTraverser_goLeft___redArg(v_t_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg___lam__0(lean_object* v_s_2281_){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_box(0);
v___x_2283_ = l_Lean_Syntax_Traverser_right(v_s_2281_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight___redArg(lean_object* v_t_2286_){
_start:
{
lean_object* v_modifyGet_2287_; lean_object* v___f_2288_; lean_object* v___x_2289_; 
v_modifyGet_2287_ = lean_ctor_get(v_t_2286_, 2);
lean_inc(v_modifyGet_2287_);
lean_dec_ref(v_t_2286_);
v___f_2288_ = ((lean_object*)(l_Lean_Syntax_MonadTraverser_goRight___redArg___closed__0));
v___x_2289_ = lean_apply_2(v_modifyGet_2287_, lean_box(0), v___f_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_goRight(lean_object* v_m_2290_, lean_object* v_t_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_Syntax_MonadTraverser_goRight___redArg(v_t_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(lean_object* v_toPure_2293_, lean_object* v_st_2294_){
_start:
{
lean_object* v_idxs_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v_idxs_2295_ = lean_ctor_get(v_st_2294_, 2);
v___x_2296_ = lean_array_get_size(v_idxs_2295_);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_nat_sub(v___x_2296_, v___x_2297_);
v___x_2299_ = lean_nat_dec_lt(v___x_2298_, v___x_2296_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec(v___x_2298_);
v___x_2300_ = lean_unsigned_to_nat(0u);
v___x_2301_ = lean_apply_2(v_toPure_2293_, lean_box(0), v___x_2300_);
return v___x_2301_;
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = lean_array_fget_borrowed(v_idxs_2295_, v___x_2298_);
lean_dec(v___x_2298_);
lean_inc(v___x_2302_);
v___x_2303_ = lean_apply_2(v_toPure_2293_, lean_box(0), v___x_2302_);
return v___x_2303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed(lean_object* v_toPure_2304_, lean_object* v_st_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0(v_toPure_2304_, v_st_2305_);
lean_dec_ref(v_st_2305_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx___redArg(lean_object* v_inst_2307_, lean_object* v_t_2308_){
_start:
{
lean_object* v_toApplicative_2309_; lean_object* v_toBind_2310_; lean_object* v_get_2311_; lean_object* v_toPure_2312_; lean_object* v___f_2313_; lean_object* v___x_2314_; 
v_toApplicative_2309_ = lean_ctor_get(v_inst_2307_, 0);
lean_inc_ref(v_toApplicative_2309_);
v_toBind_2310_ = lean_ctor_get(v_inst_2307_, 1);
lean_inc(v_toBind_2310_);
lean_dec_ref(v_inst_2307_);
v_get_2311_ = lean_ctor_get(v_t_2308_, 0);
lean_inc(v_get_2311_);
lean_dec_ref(v_t_2308_);
v_toPure_2312_ = lean_ctor_get(v_toApplicative_2309_, 1);
lean_inc(v_toPure_2312_);
lean_dec_ref(v_toApplicative_2309_);
v___f_2313_ = lean_alloc_closure((void*)(l_Lean_Syntax_MonadTraverser_getIdx___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2313_, 0, v_toPure_2312_);
v___x_2314_ = lean_apply_4(v_toBind_2310_, lean_box(0), lean_box(0), v_get_2311_, v___f_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_MonadTraverser_getIdx(lean_object* v_m_2315_, lean_object* v_inst_2316_, lean_object* v_t_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_Syntax_MonadTraverser_getIdx___redArg(v_inst_2316_, v_t_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt(lean_object* v_n_2319_, lean_object* v_i_2320_){
_start:
{
lean_object* v_args_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_args_2321_ = lean_ctor_get(v_n_2319_, 2);
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_array_get_borrowed(v___x_2322_, v_args_2321_, v_i_2320_);
v___x_2324_ = l_Lean_Syntax_getId(v___x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_SyntaxNode_getIdAt___boxed(lean_object* v_n_2325_, lean_object* v_i_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_SyntaxNode_getIdAt(v_n_2325_, v_i_2326_);
lean_dec(v_i_2326_);
lean_dec(v_n_2325_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkListNode(lean_object* v_args_2328_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2329_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2330_ = lean_box(2);
v___x_2331_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
lean_ctor_set(v___x_2331_, 1, v___x_2329_);
lean_ctor_set(v___x_2331_, 2, v_args_2328_);
return v___x_2331_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isQuot(lean_object* v_x_2337_){
_start:
{
if (lean_obj_tag(v_x_2337_) == 1)
{
lean_object* v_kind_2338_; 
v_kind_2338_ = lean_ctor_get(v_x_2337_, 1);
if (lean_obj_tag(v_kind_2338_) == 1)
{
lean_object* v_pre_2339_; lean_object* v_str_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v_pre_2339_ = lean_ctor_get(v_kind_2338_, 0);
v_str_2340_ = lean_ctor_get(v_kind_2338_, 1);
v___x_2341_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__0));
v___x_2342_ = lean_string_dec_eq(v_str_2340_, v___x_2341_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
v___x_2343_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__1));
v___x_2344_ = lean_string_dec_eq(v_str_2340_, v___x_2343_);
if (v___x_2344_ == 0)
{
return v___x_2344_;
}
else
{
if (lean_obj_tag(v_pre_2339_) == 1)
{
lean_object* v_pre_2345_; 
v_pre_2345_ = lean_ctor_get(v_pre_2339_, 0);
if (lean_obj_tag(v_pre_2345_) == 1)
{
lean_object* v_pre_2346_; 
v_pre_2346_ = lean_ctor_get(v_pre_2345_, 0);
if (lean_obj_tag(v_pre_2346_) == 1)
{
lean_object* v_pre_2347_; 
v_pre_2347_ = lean_ctor_get(v_pre_2346_, 0);
if (lean_obj_tag(v_pre_2347_) == 0)
{
lean_object* v_str_2348_; lean_object* v_str_2349_; lean_object* v_str_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_str_2348_ = lean_ctor_get(v_pre_2339_, 1);
v_str_2349_ = lean_ctor_get(v_pre_2345_, 1);
v_str_2350_ = lean_ctor_get(v_pre_2346_, 1);
v___x_2351_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__2));
v___x_2352_ = lean_string_dec_eq(v_str_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
return v___x_2342_;
}
else
{
lean_object* v___x_2353_; uint8_t v___x_2354_; 
v___x_2353_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__3));
v___x_2354_ = lean_string_dec_eq(v_str_2349_, v___x_2353_);
if (v___x_2354_ == 0)
{
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; uint8_t v___x_2356_; 
v___x_2355_ = ((lean_object*)(l_Lean_Syntax_isQuot___closed__4));
v___x_2356_ = lean_string_dec_eq(v_str_2348_, v___x_2355_);
return v___x_2356_;
}
}
}
else
{
return v___x_2342_;
}
}
else
{
return v___x_2342_;
}
}
else
{
return v___x_2342_;
}
}
else
{
return v___x_2342_;
}
}
}
else
{
return v___x_2342_;
}
}
else
{
uint8_t v___x_2357_; 
v___x_2357_ = 0;
return v___x_2357_;
}
}
else
{
uint8_t v___x_2358_; 
v___x_2358_ = 0;
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isQuot___boxed(lean_object* v_x_2359_){
_start:
{
uint8_t v_res_2360_; lean_object* v_r_2361_; 
v_res_2360_ = l_Lean_Syntax_isQuot(v_x_2359_);
lean_dec(v_x_2359_);
v_r_2361_ = lean_box(v_res_2360_);
return v_r_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getQuotContent(lean_object* v_stx_2367_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___y_2371_; uint8_t v___x_2377_; 
v___x_2368_ = l_Lean_Syntax_getNumArgs(v_stx_2367_);
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2377_ = lean_nat_dec_eq(v___x_2368_, v___x_2369_);
lean_dec(v___x_2368_);
if (v___x_2377_ == 0)
{
v___y_2371_ = v_stx_2367_;
goto v___jp_2370_;
}
else
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_unsigned_to_nat(0u);
v___x_2379_ = l_Lean_Syntax_getArg(v_stx_2367_, v___x_2378_);
lean_dec(v_stx_2367_);
v___y_2371_ = v___x_2379_;
goto v___jp_2370_;
}
v___jp_2370_:
{
lean_object* v___x_2372_; uint8_t v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Lean_Syntax_getQuotContent___closed__0));
lean_inc(v___y_2371_);
v___x_2373_ = l_Lean_Syntax_isOfKind(v___y_2371_, v___x_2372_);
if (v___x_2373_ == 0)
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Syntax_getArg(v___y_2371_, v___x_2369_);
lean_dec(v___y_2371_);
return v___x_2374_;
}
else
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_unsigned_to_nat(3u);
v___x_2376_ = l_Lean_Syntax_getArg(v___y_2371_, v___x_2375_);
lean_dec(v___y_2371_);
return v___x_2376_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquot(lean_object* v_x_2381_){
_start:
{
if (lean_obj_tag(v_x_2381_) == 1)
{
lean_object* v_kind_2382_; 
v_kind_2382_ = lean_ctor_get(v_x_2381_, 1);
if (lean_obj_tag(v_kind_2382_) == 1)
{
lean_object* v_str_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; 
v_str_2383_ = lean_ctor_get(v_kind_2382_, 1);
v___x_2384_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2385_ = lean_string_dec_eq(v_str_2383_, v___x_2384_);
return v___x_2385_;
}
else
{
uint8_t v___x_2386_; 
v___x_2386_ = 0;
return v___x_2386_;
}
}
else
{
uint8_t v___x_2387_; 
v___x_2387_ = 0;
return v___x_2387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquot___boxed(lean_object* v_x_2388_){
_start:
{
uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_res_2389_ = l_Lean_Syntax_isAntiquot(v_x_2388_);
lean_dec(v_x_2388_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(lean_object* v___x_2391_, uint8_t v___x_2392_, lean_object* v_as_2393_, size_t v_i_2394_, size_t v_stop_2395_){
_start:
{
uint8_t v___x_2396_; 
v___x_2396_ = lean_usize_dec_eq(v_i_2394_, v_stop_2395_);
if (v___x_2396_ == 0)
{
uint8_t v___x_2397_; uint8_t v___y_2399_; lean_object* v___x_2403_; uint8_t v___x_2404_; 
v___x_2397_ = 1;
v___x_2403_ = lean_array_uget_borrowed(v_as_2393_, v_i_2394_);
v___x_2404_ = l_Lean_Syntax_isAntiquot(v___x_2403_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
v___x_2405_ = lean_unsigned_to_nat(0u);
v___x_2406_ = lean_nat_dec_lt(v___x_2405_, v___x_2391_);
v___y_2399_ = v___x_2406_;
goto v___jp_2398_;
}
else
{
v___y_2399_ = v___x_2392_;
goto v___jp_2398_;
}
v___jp_2398_:
{
if (v___y_2399_ == 0)
{
size_t v___x_2400_; size_t v___x_2401_; 
v___x_2400_ = ((size_t)1ULL);
v___x_2401_ = lean_usize_add(v_i_2394_, v___x_2400_);
v_i_2394_ = v___x_2401_;
goto _start;
}
else
{
return v___x_2397_;
}
}
}
else
{
uint8_t v___x_2407_; 
v___x_2407_ = 0;
return v___x_2407_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0___boxed(lean_object* v___x_2408_, lean_object* v___x_2409_, lean_object* v_as_2410_, lean_object* v_i_2411_, lean_object* v_stop_2412_){
_start:
{
uint8_t v___x_341__boxed_2413_; size_t v_i_boxed_2414_; size_t v_stop_boxed_2415_; uint8_t v_res_2416_; lean_object* v_r_2417_; 
v___x_341__boxed_2413_ = lean_unbox(v___x_2409_);
v_i_boxed_2414_ = lean_unbox_usize(v_i_2411_);
lean_dec(v_i_2411_);
v_stop_boxed_2415_ = lean_unbox_usize(v_stop_2412_);
lean_dec(v_stop_2412_);
v_res_2416_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2408_, v___x_341__boxed_2413_, v_as_2410_, v_i_boxed_2414_, v_stop_boxed_2415_);
lean_dec_ref(v_as_2410_);
lean_dec(v___x_2408_);
v_r_2417_ = lean_box(v_res_2416_);
return v_r_2417_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquots(lean_object* v_stx_2418_){
_start:
{
uint8_t v___x_2419_; 
v___x_2419_ = l_Lean_Syntax_isAntiquot(v_stx_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; uint8_t v___x_2421_; 
v___x_2420_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2418_);
v___x_2421_ = l_Lean_Syntax_isOfKind(v_stx_2418_, v___x_2420_);
if (v___x_2421_ == 0)
{
lean_dec(v_stx_2418_);
return v___x_2421_;
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = l_Lean_Syntax_getNumArgs(v_stx_2418_);
v___x_2424_ = lean_nat_dec_lt(v___x_2422_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_dec(v___x_2423_);
lean_dec(v_stx_2418_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2425_ = l_Lean_Syntax_getArgs(v_stx_2418_);
lean_dec(v_stx_2418_);
v___x_2426_ = lean_array_get_size(v___x_2425_);
v___x_2427_ = lean_nat_dec_lt(v___x_2422_, v___x_2426_);
if (v___x_2427_ == 0)
{
lean_dec_ref(v___x_2425_);
lean_dec(v___x_2423_);
return v___x_2424_;
}
else
{
if (v___x_2427_ == 0)
{
lean_dec_ref(v___x_2425_);
lean_dec(v___x_2423_);
return v___x_2424_;
}
else
{
size_t v___x_2428_; size_t v___x_2429_; uint8_t v___x_2430_; 
v___x_2428_ = ((size_t)0ULL);
v___x_2429_ = lean_usize_of_nat(v___x_2426_);
v___x_2430_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Syntax_isAntiquots_spec__0(v___x_2423_, v___x_2419_, v___x_2425_, v___x_2428_, v___x_2429_);
lean_dec_ref(v___x_2425_);
lean_dec(v___x_2423_);
if (v___x_2430_ == 0)
{
return v___x_2427_;
}
else
{
return v___x_2419_;
}
}
}
}
}
}
else
{
lean_dec(v_stx_2418_);
return v___x_2419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquots___boxed(lean_object* v_stx_2431_){
_start:
{
uint8_t v_res_2432_; lean_object* v_r_2433_; 
v_res_2432_ = l_Lean_Syntax_isAntiquots(v_stx_2431_);
v_r_2433_ = lean_box(v_res_2432_);
return v_r_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getCanonicalAntiquot(lean_object* v_stx_2434_){
_start:
{
lean_object* v___x_2435_; uint8_t v___x_2436_; 
v___x_2435_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2434_);
v___x_2436_ = l_Lean_Syntax_isOfKind(v_stx_2434_, v___x_2435_);
if (v___x_2436_ == 0)
{
return v_stx_2434_;
}
else
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_unsigned_to_nat(0u);
v___x_2438_ = l_Lean_Syntax_getArg(v_stx_2434_, v___x_2437_);
lean_dec(v_stx_2434_);
return v___x_2438_;
}
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__1(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__0));
v___x_2441_ = l_Lean_mkAtom(v___x_2440_);
return v___x_2441_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__3(void){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2444_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2445_ = lean_unsigned_to_nat(4u);
v___x_2446_ = lean_mk_empty_array_with_capacity(v___x_2445_);
v___x_2447_ = lean_array_push(v___x_2446_, v___x_2444_);
return v___x_2447_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__9(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__8));
v___x_2456_ = l_Lean_mkAtom(v___x_2455_);
return v___x_2456_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__10(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2457_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__9, &l_Lean_Syntax_mkAntiquotNode___closed__9_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__9);
v___x_2458_ = lean_unsigned_to_nat(2u);
v___x_2459_ = lean_mk_empty_array_with_capacity(v___x_2458_);
v___x_2460_ = lean_array_push(v___x_2459_, v___x_2457_);
return v___x_2460_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__16(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__15));
v___x_2472_ = l_Lean_mkAtom(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__18(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__17));
v___x_2475_ = l_Lean_mkAtom(v___x_2474_);
return v___x_2475_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotNode___closed__19(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2476_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__16, &l_Lean_Syntax_mkAntiquotNode___closed__16_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__16);
v___x_2477_ = lean_unsigned_to_nat(3u);
v___x_2478_ = lean_mk_empty_array_with_capacity(v___x_2477_);
v___x_2479_ = lean_array_push(v___x_2478_, v___x_2476_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode(lean_object* v_kind_2480_, lean_object* v_term_2481_, lean_object* v_nesting_2482_, lean_object* v_name_2483_, uint8_t v_isPseudoKind_2484_){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_nesting_2489_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2508_; uint8_t v___x_2516_; 
v___x_2485_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2486_ = lean_mk_array(v_nesting_2482_, v___x_2485_);
v___x_2487_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2488_ = lean_box(2);
v_nesting_2489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2489_, 0, v___x_2488_);
lean_ctor_set(v_nesting_2489_, 1, v___x_2487_);
lean_ctor_set(v_nesting_2489_, 2, v___x_2486_);
v___x_2516_ = l_Lean_Syntax_isIdent(v_term_2481_);
if (v___x_2516_ == 0)
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
lean_inc(v_term_2481_);
v___x_2518_ = l_Lean_Syntax_isOfKind(v_term_2481_, v___x_2517_);
if (v___x_2518_ == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2519_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__14));
v___x_2520_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__18, &l_Lean_Syntax_mkAntiquotNode___closed__18_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__18);
v___x_2521_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__19, &l_Lean_Syntax_mkAntiquotNode___closed__19_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__19);
v___x_2522_ = lean_array_push(v___x_2521_, v_term_2481_);
v___x_2523_ = lean_array_push(v___x_2522_, v___x_2520_);
v___x_2524_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2488_);
lean_ctor_set(v___x_2524_, 1, v___x_2519_);
lean_ctor_set(v___x_2524_, 2, v___x_2523_);
v___y_2508_ = v___x_2524_;
goto v___jp_2507_;
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_unsigned_to_nat(0u);
v___x_2526_ = l_Lean_Syntax_getArg(v_term_2481_, v___x_2525_);
lean_dec(v_term_2481_);
v___y_2508_ = v___x_2526_;
goto v___jp_2507_;
}
}
else
{
v___y_2508_ = v_term_2481_;
goto v___jp_2507_;
}
v___jp_2490_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_inc(v___y_2493_);
v___x_2494_ = l_Lean_Name_append(v_kind_2480_, v___y_2493_);
v___x_2495_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__2));
v___x_2496_ = l_Lean_Name_append(v___x_2494_, v___x_2495_);
v___x_2497_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__3, &l_Lean_Syntax_mkAntiquotNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__3);
v___x_2498_ = lean_array_push(v___x_2497_, v_nesting_2489_);
v___x_2499_ = lean_array_push(v___x_2498_, v___y_2492_);
v___x_2500_ = lean_array_push(v___x_2499_, v___y_2491_);
v___x_2501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2488_);
lean_ctor_set(v___x_2501_, 1, v___x_2496_);
lean_ctor_set(v___x_2501_, 2, v___x_2500_);
return v___x_2501_;
}
v___jp_2502_:
{
if (v_isPseudoKind_2484_ == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_box(0);
v___y_2491_ = v___y_2504_;
v___y_2492_ = v___y_2503_;
v___y_2493_ = v___x_2505_;
goto v___jp_2490_;
}
else
{
lean_object* v___x_2506_; 
v___x_2506_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__5));
v___y_2491_ = v___y_2504_;
v___y_2492_ = v___y_2503_;
v___y_2493_ = v___x_2506_;
goto v___jp_2490_;
}
}
v___jp_2507_:
{
if (lean_obj_tag(v_name_2483_) == 0)
{
lean_object* v___x_2509_; 
v___x_2509_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__3));
v___y_2503_ = v___y_2508_;
v___y_2504_ = v___x_2509_;
goto v___jp_2502_;
}
else
{
lean_object* v_val_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_val_2510_ = lean_ctor_get(v_name_2483_, 0);
lean_inc(v_val_2510_);
lean_dec_ref_known(v_name_2483_, 1);
v___x_2511_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__7));
v___x_2512_ = l_Lean_mkAtom(v_val_2510_);
v___x_2513_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__10, &l_Lean_Syntax_mkAntiquotNode___closed__10_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__10);
v___x_2514_ = lean_array_push(v___x_2513_, v___x_2512_);
v___x_2515_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2488_);
lean_ctor_set(v___x_2515_, 1, v___x_2511_);
lean_ctor_set(v___x_2515_, 2, v___x_2514_);
v___y_2503_ = v___y_2508_;
v___y_2504_ = v___x_2515_;
goto v___jp_2502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotNode___boxed(lean_object* v_kind_2527_, lean_object* v_term_2528_, lean_object* v_nesting_2529_, lean_object* v_name_2530_, lean_object* v_isPseudoKind_2531_){
_start:
{
uint8_t v_isPseudoKind_boxed_2532_; lean_object* v_res_2533_; 
v_isPseudoKind_boxed_2532_ = lean_unbox(v_isPseudoKind_2531_);
v_res_2533_ = l_Lean_Syntax_mkAntiquotNode(v_kind_2527_, v_term_2528_, v_nesting_2529_, v_name_2530_, v_isPseudoKind_boxed_2532_);
return v_res_2533_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isEscapedAntiquot(lean_object* v_stx_2534_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2535_ = lean_unsigned_to_nat(1u);
v___x_2536_ = l_Lean_Syntax_getArg(v_stx_2534_, v___x_2535_);
v___x_2537_ = l_Lean_Syntax_getArgs(v___x_2536_);
lean_dec(v___x_2536_);
v___x_2538_ = lean_array_get_size(v___x_2537_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = lean_unsigned_to_nat(0u);
v___x_2540_ = lean_nat_dec_eq(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
uint8_t v___x_2541_; 
v___x_2541_ = 1;
return v___x_2541_;
}
else
{
uint8_t v___x_2542_; 
v___x_2542_ = 0;
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isEscapedAntiquot___boxed(lean_object* v_stx_2543_){
_start:
{
uint8_t v_res_2544_; lean_object* v_r_2545_; 
v_res_2544_ = l_Lean_Syntax_isEscapedAntiquot(v_stx_2543_);
lean_dec(v_stx_2543_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_unescapeAntiquot(lean_object* v_stx_2546_){
_start:
{
uint8_t v___x_2547_; 
v___x_2547_ = l_Lean_Syntax_isAntiquot(v_stx_2546_);
if (v___x_2547_ == 0)
{
return v_stx_2546_;
}
else
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = l_Lean_Syntax_getArg(v_stx_2546_, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_getArgs(v___x_2549_);
lean_dec(v___x_2549_);
v___x_2551_ = lean_array_pop(v___x_2550_);
v___x_2552_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2553_ = lean_box(2);
v___x_2554_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___x_2552_);
lean_ctor_set(v___x_2554_, 2, v___x_2551_);
v___x_2555_ = l_Lean_Syntax_setArg(v_stx_2546_, v___x_2548_, v___x_2554_);
return v___x_2555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm(lean_object* v_stx_2556_){
_start:
{
lean_object* v___y_2558_; uint8_t v___x_2569_; 
v___x_2569_ = l_Lean_Syntax_isAntiquot(v_stx_2556_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_unsigned_to_nat(3u);
v___x_2571_ = l_Lean_Syntax_getArg(v_stx_2556_, v___x_2570_);
v___y_2558_ = v___x_2571_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2572_ = lean_unsigned_to_nat(2u);
v___x_2573_ = l_Lean_Syntax_getArg(v_stx_2556_, v___x_2572_);
v___y_2558_ = v___x_2573_;
goto v___jp_2557_;
}
v___jp_2557_:
{
uint8_t v___x_2559_; 
v___x_2559_ = l_Lean_Syntax_isIdent(v___y_2558_);
if (v___x_2559_ == 0)
{
uint8_t v___x_2560_; 
v___x_2560_ = l_Lean_Syntax_isAtom(v___y_2558_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_unsigned_to_nat(1u);
v___x_2562_ = l_Lean_Syntax_getArg(v___y_2558_, v___x_2561_);
lean_dec(v___y_2558_);
return v___x_2562_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2563_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__12));
v___x_2564_ = lean_unsigned_to_nat(1u);
v___x_2565_ = lean_mk_empty_array_with_capacity(v___x_2564_);
v___x_2566_ = lean_array_push(v___x_2565_, v___y_2558_);
v___x_2567_ = lean_box(2);
v___x_2568_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2568_, 0, v___x_2567_);
lean_ctor_set(v___x_2568_, 1, v___x_2563_);
lean_ctor_set(v___x_2568_, 2, v___x_2566_);
return v___x_2568_;
}
}
else
{
return v___y_2558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotTerm___boxed(lean_object* v_stx_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Syntax_getAntiquotTerm(v_stx_2574_);
lean_dec(v_stx_2574_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f(lean_object* v_x_2576_){
_start:
{
if (lean_obj_tag(v_x_2576_) == 1)
{
lean_object* v_kind_2577_; 
v_kind_2577_ = lean_ctor_get(v_x_2576_, 1);
if (lean_obj_tag(v_kind_2577_) == 1)
{
lean_object* v_pre_2578_; lean_object* v_str_2579_; 
v_pre_2578_ = lean_ctor_get(v_kind_2577_, 0);
v_str_2579_ = lean_ctor_get(v_kind_2577_, 1);
if (lean_obj_tag(v_pre_2578_) == 1)
{
lean_object* v_pre_2585_; lean_object* v_str_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v_pre_2585_ = lean_ctor_get(v_pre_2578_, 0);
v_str_2586_ = lean_ctor_get(v_pre_2578_, 1);
v___x_2587_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotNode___closed__4));
v___x_2588_ = lean_string_dec_eq(v_str_2586_, v___x_2587_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2590_ = lean_string_dec_eq(v_str_2579_, v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = lean_box(0);
return v___x_2591_;
}
else
{
goto v___jp_2580_;
}
}
else
{
lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2592_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2593_ = lean_string_dec_eq(v_str_2579_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_box(0);
return v___x_2594_;
}
else
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_box(v___x_2593_);
lean_inc(v_pre_2585_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_pre_2585_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
}
else
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = ((lean_object*)(l_Lean_Syntax_isAntiquot___closed__0));
v___x_2599_ = lean_string_dec_eq(v_str_2579_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_box(0);
return v___x_2600_;
}
else
{
goto v___jp_2580_;
}
}
v___jp_2580_:
{
uint8_t v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2581_ = 0;
v___x_2582_ = lean_box(v___x_2581_);
lean_inc(v_pre_2578_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v_pre_2578_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
}
else
{
lean_object* v___x_2601_; 
v___x_2601_ = lean_box(0);
return v___x_2601_;
}
}
else
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_box(0);
return v___x_2602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKind_x3f___boxed(lean_object* v_x_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_Syntax_antiquotKind_x3f(v_x_2603_);
lean_dec(v_x_2603_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(lean_object* v_as_2605_, size_t v_i_2606_, size_t v_stop_2607_, lean_object* v_b_2608_){
_start:
{
lean_object* v___y_2610_; uint8_t v___x_2614_; 
v___x_2614_ = lean_usize_dec_eq(v_i_2606_, v_stop_2607_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2615_ = lean_array_uget_borrowed(v_as_2605_, v_i_2606_);
v___x_2616_ = l_Lean_Syntax_antiquotKind_x3f(v___x_2615_);
if (lean_obj_tag(v___x_2616_) == 0)
{
v___y_2610_ = v_b_2608_;
goto v___jp_2609_;
}
else
{
lean_object* v_val_2617_; lean_object* v___x_2618_; 
v_val_2617_ = lean_ctor_get(v___x_2616_, 0);
lean_inc(v_val_2617_);
lean_dec_ref_known(v___x_2616_, 1);
v___x_2618_ = lean_array_push(v_b_2608_, v_val_2617_);
v___y_2610_ = v___x_2618_;
goto v___jp_2609_;
}
}
else
{
return v_b_2608_;
}
v___jp_2609_:
{
size_t v___x_2611_; size_t v___x_2612_; 
v___x_2611_ = ((size_t)1ULL);
v___x_2612_ = lean_usize_add(v_i_2606_, v___x_2611_);
v_i_2606_ = v___x_2612_;
v_b_2608_ = v___y_2610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0___boxed(lean_object* v_as_2619_, lean_object* v_i_2620_, lean_object* v_stop_2621_, lean_object* v_b_2622_){
_start:
{
size_t v_i_boxed_2623_; size_t v_stop_boxed_2624_; lean_object* v_res_2625_; 
v_i_boxed_2623_ = lean_unbox_usize(v_i_2620_);
lean_dec(v_i_2620_);
v_stop_boxed_2624_ = lean_unbox_usize(v_stop_2621_);
lean_dec(v_stop_2621_);
v_res_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2619_, v_i_boxed_2623_, v_stop_boxed_2624_, v_b_2622_);
lean_dec_ref(v_as_2619_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(lean_object* v_as_2628_, lean_object* v_start_2629_, lean_object* v_stop_2630_){
_start:
{
lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2631_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___closed__0));
v___x_2632_ = lean_nat_dec_lt(v_start_2629_, v_stop_2630_);
if (v___x_2632_ == 0)
{
return v___x_2631_;
}
else
{
lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2633_ = lean_array_get_size(v_as_2628_);
v___x_2634_ = lean_nat_dec_le(v_stop_2630_, v___x_2633_);
if (v___x_2634_ == 0)
{
uint8_t v___x_2635_; 
v___x_2635_ = lean_nat_dec_lt(v_start_2629_, v___x_2633_);
if (v___x_2635_ == 0)
{
return v___x_2631_;
}
else
{
size_t v___x_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
v___x_2636_ = lean_usize_of_nat(v_start_2629_);
v___x_2637_ = lean_usize_of_nat(v___x_2633_);
v___x_2638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2628_, v___x_2636_, v___x_2637_, v___x_2631_);
return v___x_2638_;
}
}
else
{
size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; 
v___x_2639_ = lean_usize_of_nat(v_start_2629_);
v___x_2640_ = lean_usize_of_nat(v_stop_2630_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0_spec__0(v_as_2628_, v___x_2639_, v___x_2640_, v___x_2631_);
return v___x_2641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0___boxed(lean_object* v_as_2642_, lean_object* v_start_2643_, lean_object* v_stop_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v_as_2642_, v_start_2643_, v_stop_2644_);
lean_dec(v_stop_2644_);
lean_dec(v_start_2643_);
lean_dec_ref(v_as_2642_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotKinds(lean_object* v_stx_2646_){
_start:
{
lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2647_ = ((lean_object*)(l_Lean_Syntax_instForInTopDownOfMonad_loop___redArg___lam__4___closed__1));
lean_inc(v_stx_2646_);
v___x_2648_ = l_Lean_Syntax_isOfKind(v_stx_2646_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_Syntax_antiquotKind_x3f(v_stx_2646_);
lean_dec(v_stx_2646_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v___x_2650_; 
v___x_2650_ = lean_box(0);
return v___x_2650_;
}
else
{
lean_object* v_val_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_val_2651_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2652_ = lean_box(0);
v___x_2653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_val_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2652_);
return v___x_2653_;
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2654_ = l_Lean_Syntax_getArgs(v_stx_2646_);
lean_dec(v_stx_2646_);
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_array_get_size(v___x_2654_);
v___x_2657_ = l_Array_filterMapM___at___00Lean_Syntax_antiquotKinds_spec__0(v___x_2654_, v___x_2655_, v___x_2656_);
lean_dec_ref(v___x_2654_);
v___x_2658_ = lean_array_to_list(v___x_2657_);
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f(lean_object* v_x_2660_){
_start:
{
if (lean_obj_tag(v_x_2660_) == 1)
{
lean_object* v_kind_2661_; 
v_kind_2661_ = lean_ctor_get(v_x_2660_, 1);
if (lean_obj_tag(v_kind_2661_) == 1)
{
lean_object* v_pre_2662_; lean_object* v_str_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
v_pre_2662_ = lean_ctor_get(v_kind_2661_, 0);
v_str_2663_ = lean_ctor_get(v_kind_2661_, 1);
v___x_2664_ = ((lean_object*)(l_Lean_Syntax_antiquotSpliceKind_x3f___closed__0));
v___x_2665_ = lean_string_dec_eq(v_str_2663_, v___x_2664_);
if (v___x_2665_ == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_box(0);
return v___x_2666_;
}
else
{
lean_object* v___x_2667_; 
lean_inc(v_pre_2662_);
v___x_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_pre_2662_);
return v___x_2667_;
}
}
else
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_box(0);
return v___x_2668_;
}
}
else
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_box(0);
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSpliceKind_x3f___boxed(lean_object* v_x_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_x_2670_);
lean_dec(v_x_2670_);
return v_res_2671_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSplice(lean_object* v_stx_2672_){
_start:
{
lean_object* v___x_2673_; 
v___x_2673_ = l_Lean_Syntax_antiquotSpliceKind_x3f(v_stx_2672_);
if (lean_obj_tag(v___x_2673_) == 0)
{
uint8_t v___x_2674_; 
v___x_2674_ = 0;
return v___x_2674_;
}
else
{
uint8_t v___x_2675_; 
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = 1;
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSplice___boxed(lean_object* v_stx_2676_){
_start:
{
uint8_t v_res_2677_; lean_object* v_r_2678_; 
v_res_2677_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2676_);
lean_dec(v_stx_2676_);
v_r_2678_ = lean_box(v_res_2677_);
return v_r_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents(lean_object* v_stx_2679_){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_unsigned_to_nat(3u);
v___x_2681_ = l_Lean_Syntax_getArg(v_stx_2679_, v___x_2680_);
v___x_2682_ = l_Lean_Syntax_getArgs(v___x_2681_);
lean_dec(v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceContents___boxed(lean_object* v_stx_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l_Lean_Syntax_getAntiquotSpliceContents(v_stx_2683_);
lean_dec(v_stx_2683_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix(lean_object* v_stx_2685_){
_start:
{
uint8_t v___x_2686_; 
v___x_2686_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = l_Lean_Syntax_getArg(v_stx_2685_, v___x_2687_);
return v___x_2688_;
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_unsigned_to_nat(5u);
v___x_2690_ = l_Lean_Syntax_getArg(v_stx_2685_, v___x_2689_);
return v___x_2690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSpliceSuffix___boxed(lean_object* v_stx_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_Syntax_getAntiquotSpliceSuffix(v_stx_2691_);
lean_dec(v_stx_2691_);
return v_res_2692_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__2));
v___x_2698_ = l_Lean_mkAtom(v___x_2697_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__4));
v___x_2701_ = l_Lean_mkAtom(v___x_2700_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2702_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2703_ = lean_unsigned_to_nat(6u);
v___x_2704_ = lean_mk_empty_array_with_capacity(v___x_2703_);
v___x_2705_ = lean_array_push(v___x_2704_, v___x_2702_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSpliceNode(lean_object* v_kind_2706_, lean_object* v_contents_2707_, lean_object* v_suffix_2708_, lean_object* v_nesting_2709_){
_start:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v_nesting_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2710_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotNode___closed__1, &l_Lean_Syntax_mkAntiquotNode___closed__1_once, _init_l_Lean_Syntax_mkAntiquotNode___closed__1);
v___x_2711_ = lean_mk_array(v_nesting_2709_, v___x_2710_);
v___x_2712_ = ((lean_object*)(l_Lean_Syntax_asNode___closed__2));
v___x_2713_ = lean_box(2);
v_nesting_2714_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_nesting_2714_, 0, v___x_2713_);
lean_ctor_set(v_nesting_2714_, 1, v___x_2712_);
lean_ctor_set(v_nesting_2714_, 2, v___x_2711_);
v___x_2715_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSpliceNode___closed__1));
v___x_2716_ = l_Lean_Name_append(v_kind_2706_, v___x_2715_);
v___x_2717_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__3, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__3_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__3);
v___x_2718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2713_);
lean_ctor_set(v___x_2718_, 1, v___x_2712_);
lean_ctor_set(v___x_2718_, 2, v_contents_2707_);
v___x_2719_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__5, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__5_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__5);
v___x_2720_ = l_Lean_mkAtom(v_suffix_2708_);
v___x_2721_ = lean_obj_once(&l_Lean_Syntax_mkAntiquotSpliceNode___closed__6, &l_Lean_Syntax_mkAntiquotSpliceNode___closed__6_once, _init_l_Lean_Syntax_mkAntiquotSpliceNode___closed__6);
v___x_2722_ = lean_array_push(v___x_2721_, v_nesting_2714_);
v___x_2723_ = lean_array_push(v___x_2722_, v___x_2717_);
v___x_2724_ = lean_array_push(v___x_2723_, v___x_2718_);
v___x_2725_ = lean_array_push(v___x_2724_, v___x_2719_);
v___x_2726_ = lean_array_push(v___x_2725_, v___x_2720_);
v___x_2727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2713_);
lean_ctor_set(v___x_2727_, 1, v___x_2716_);
lean_ctor_set(v___x_2727_, 2, v___x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f(lean_object* v_x_2729_){
_start:
{
if (lean_obj_tag(v_x_2729_) == 1)
{
lean_object* v_kind_2730_; 
v_kind_2730_ = lean_ctor_get(v_x_2729_, 1);
if (lean_obj_tag(v_kind_2730_) == 1)
{
lean_object* v_pre_2731_; lean_object* v_str_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_pre_2731_ = lean_ctor_get(v_kind_2730_, 0);
v_str_2732_ = lean_ctor_get(v_kind_2730_, 1);
v___x_2733_ = ((lean_object*)(l_Lean_Syntax_antiquotSuffixSplice_x3f___closed__0));
v___x_2734_ = lean_string_dec_eq(v_str_2732_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_box(0);
return v___x_2735_;
}
else
{
lean_object* v___x_2736_; 
lean_inc(v_pre_2731_);
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_pre_2731_);
return v___x_2736_;
}
}
else
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_box(0);
return v___x_2737_;
}
}
else
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_box(0);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_antiquotSuffixSplice_x3f___boxed(lean_object* v_x_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_x_2739_);
lean_dec(v_x_2739_);
return v_res_2740_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAntiquotSuffixSplice(lean_object* v_stx_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_Syntax_antiquotSuffixSplice_x3f(v_stx_2741_);
if (lean_obj_tag(v___x_2742_) == 0)
{
uint8_t v___x_2743_; 
v___x_2743_ = 0;
return v___x_2743_;
}
else
{
uint8_t v___x_2744_; 
lean_dec_ref_known(v___x_2742_, 1);
v___x_2744_ = 1;
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAntiquotSuffixSplice___boxed(lean_object* v_stx_2745_){
_start:
{
uint8_t v_res_2746_; lean_object* v_r_2747_; 
v_res_2746_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2745_);
lean_dec(v_stx_2745_);
v_r_2747_ = lean_box(v_res_2746_);
return v_r_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner(lean_object* v_stx_2748_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = l_Lean_Syntax_getArg(v_stx_2748_, v___x_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_getAntiquotSuffixSpliceInner___boxed(lean_object* v_stx_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_Syntax_getAntiquotSuffixSpliceInner(v_stx_2751_);
lean_dec(v_stx_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_mkAntiquotSuffixSpliceNode(lean_object* v_kind_2755_, lean_object* v_inner_2756_, lean_object* v_suffix_2757_){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2758_ = ((lean_object*)(l_Lean_Syntax_mkAntiquotSuffixSpliceNode___closed__0));
v___x_2759_ = l_Lean_Name_append(v_kind_2755_, v___x_2758_);
v___x_2760_ = l_Lean_mkAtom(v_suffix_2757_);
v___x_2761_ = lean_unsigned_to_nat(2u);
v___x_2762_ = lean_mk_empty_array_with_capacity(v___x_2761_);
v___x_2763_ = lean_array_push(v___x_2762_, v_inner_2756_);
v___x_2764_ = lean_array_push(v___x_2763_, v___x_2760_);
v___x_2765_ = lean_box(2);
v___x_2766_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2765_);
lean_ctor_set(v___x_2766_, 1, v___x_2759_);
lean_ctor_set(v___x_2766_, 2, v___x_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isTokenAntiquot(lean_object* v_stx_2770_){
_start:
{
lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Syntax_isTokenAntiquot___closed__1));
v___x_2772_ = l_Lean_Syntax_isOfKind(v_stx_2770_, v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isTokenAntiquot___boxed(lean_object* v_stx_2773_){
_start:
{
uint8_t v_res_2774_; lean_object* v_r_2775_; 
v_res_2774_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2773_);
v_r_2775_ = lean_box(v_res_2774_);
return v_r_2775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object* v_stx_2776_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = l_Lean_Syntax_isAntiquot(v_stx_2776_);
if (v___x_2777_ == 0)
{
uint8_t v___x_2778_; 
v___x_2778_ = l_Lean_Syntax_isAntiquotSplice(v_stx_2776_);
if (v___x_2778_ == 0)
{
uint8_t v___x_2779_; 
v___x_2779_ = l_Lean_Syntax_isAntiquotSuffixSplice(v_stx_2776_);
if (v___x_2779_ == 0)
{
uint8_t v___x_2780_; 
v___x_2780_ = l_Lean_Syntax_isTokenAntiquot(v_stx_2776_);
return v___x_2780_;
}
else
{
lean_dec(v_stx_2776_);
return v___x_2779_;
}
}
else
{
lean_dec(v_stx_2776_);
return v___x_2778_;
}
}
else
{
lean_dec(v_stx_2776_);
return v___x_2777_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_isAnyAntiquot___boxed(lean_object* v_stx_2781_){
_start:
{
uint8_t v_res_2782_; lean_object* v_r_2783_; 
v_res_2782_ = l_Lean_Syntax_isAnyAntiquot(v_stx_2781_);
v_r_2783_ = lean_box(v_res_2782_);
return v_r_2783_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(lean_object* v_upperBound_2787_, lean_object* v_stx_2788_, lean_object* v_visit_2789_, lean_object* v_stack_2790_, lean_object* v_accept_2791_, lean_object* v_a_2792_, lean_object* v_b_2793_){
_start:
{
lean_object* v_a_2795_; uint8_t v___x_2799_; 
v___x_2799_ = lean_nat_dec_lt(v_a_2792_, v_upperBound_2787_);
if (v___x_2799_ == 0)
{
lean_dec(v_a_2792_);
lean_dec_ref(v_accept_2791_);
lean_dec(v_stack_2790_);
lean_dec_ref(v_visit_2789_);
lean_dec(v_stx_2788_);
lean_inc_ref(v_b_2793_);
return v_b_2793_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v___x_2800_ = lean_box(0);
v___x_2801_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2802_ = l_Lean_Syntax_getArg(v_stx_2788_, v_a_2792_);
lean_inc_ref(v_visit_2789_);
lean_inc(v___x_2802_);
v___x_2803_ = lean_apply_1(v_visit_2789_, v___x_2802_);
v___x_2804_ = lean_unbox(v___x_2803_);
if (v___x_2804_ == 0)
{
lean_dec(v___x_2802_);
v_a_2795_ = v___x_2801_;
goto v___jp_2794_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_inc(v_a_2792_);
lean_inc(v_stx_2788_);
v___x_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2805_, 0, v_stx_2788_);
lean_ctor_set(v___x_2805_, 1, v_a_2792_);
lean_inc(v_stack_2790_);
v___x_2806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2805_);
lean_ctor_set(v___x_2806_, 1, v_stack_2790_);
lean_inc_ref(v_accept_2791_);
lean_inc_ref(v_visit_2789_);
v___x_2807_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2789_, v_accept_2791_, v___x_2806_, v___x_2802_);
if (lean_obj_tag(v___x_2807_) == 1)
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
lean_dec(v_a_2792_);
lean_dec_ref(v_accept_2791_);
lean_dec(v_stack_2790_);
lean_dec_ref(v_visit_2789_);
lean_dec(v_stx_2788_);
v___x_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2807_);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2808_);
lean_ctor_set(v___x_2809_, 1, v___x_2800_);
return v___x_2809_;
}
else
{
lean_dec(v___x_2807_);
v_a_2795_ = v___x_2801_;
goto v___jp_2794_;
}
}
}
v___jp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_unsigned_to_nat(1u);
v___x_2797_ = lean_nat_add(v_a_2792_, v___x_2796_);
lean_dec(v_a_2792_);
v_a_2792_ = v___x_2797_;
v_b_2793_ = v_a_2795_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(lean_object* v_visit_2810_, lean_object* v_accept_2811_, lean_object* v_stack_2812_, lean_object* v_stx_2813_){
_start:
{
lean_object* v___x_2814_; uint8_t v___x_2815_; 
lean_inc_ref(v_accept_2811_);
lean_inc(v_stx_2813_);
v___x_2814_ = lean_apply_1(v_accept_2811_, v_stx_2813_);
v___x_2815_ = lean_unbox(v___x_2814_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v_fst_2821_; 
v___x_2816_ = l_Lean_Syntax_getNumArgs(v_stx_2813_);
v___x_2817_ = lean_unsigned_to_nat(0u);
v___x_2818_ = lean_box(0);
v___x_2819_ = ((lean_object*)(l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go___closed__0));
v___x_2820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v___x_2816_, v_stx_2813_, v_visit_2810_, v_stack_2812_, v_accept_2811_, v___x_2817_, v___x_2819_);
lean_dec(v___x_2816_);
v_fst_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_fst_2821_);
lean_dec_ref(v___x_2820_);
if (lean_obj_tag(v_fst_2821_) == 0)
{
return v___x_2818_;
}
else
{
lean_object* v_val_2822_; 
v_val_2822_ = lean_ctor_get(v_fst_2821_, 0);
lean_inc(v_val_2822_);
lean_dec_ref_known(v_fst_2821_, 1);
return v_val_2822_;
}
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec_ref(v_accept_2811_);
lean_dec_ref(v_visit_2810_);
v___x_2823_ = lean_unsigned_to_nat(0u);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_stx_2813_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
lean_ctor_set(v___x_2825_, 1, v_stack_2812_);
v___x_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg___boxed(lean_object* v_upperBound_2827_, lean_object* v_stx_2828_, lean_object* v_visit_2829_, lean_object* v_stack_2830_, lean_object* v_accept_2831_, lean_object* v_a_2832_, lean_object* v_b_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2827_, v_stx_2828_, v_visit_2829_, v_stack_2830_, v_accept_2831_, v_a_2832_, v_b_2833_);
lean_dec_ref(v_b_2833_);
lean_dec(v_upperBound_2827_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(lean_object* v_upperBound_2835_, lean_object* v_stx_2836_, lean_object* v_visit_2837_, lean_object* v_stack_2838_, lean_object* v_accept_2839_, lean_object* v_inst_2840_, lean_object* v_R_2841_, lean_object* v_a_2842_, lean_object* v_b_2843_, lean_object* v_c_2844_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___redArg(v_upperBound_2835_, v_stx_2836_, v_visit_2837_, v_stack_2838_, v_accept_2839_, v_a_2842_, v_b_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0___boxed(lean_object* v_upperBound_2846_, lean_object* v_stx_2847_, lean_object* v_visit_2848_, lean_object* v_stack_2849_, lean_object* v_accept_2850_, lean_object* v_inst_2851_, lean_object* v_R_2852_, lean_object* v_a_2853_, lean_object* v_b_2854_, lean_object* v_c_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go_spec__0(v_upperBound_2846_, v_stx_2847_, v_visit_2848_, v_stack_2849_, v_accept_2850_, v_inst_2851_, v_R_2852_, v_a_2853_, v_b_2854_, v_c_2855_);
lean_dec_ref(v_b_2854_);
lean_dec(v_upperBound_2846_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_findStack_x3f(lean_object* v_root_2857_, lean_object* v_visit_2858_, lean_object* v_accept_2859_){
_start:
{
lean_object* v___x_2860_; uint8_t v___x_2861_; 
lean_inc_ref(v_visit_2858_);
lean_inc(v_root_2857_);
v___x_2860_ = lean_apply_1(v_visit_2858_, v_root_2857_);
v___x_2861_ = lean_unbox(v___x_2860_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; 
lean_dec_ref(v_accept_2859_);
lean_dec_ref(v_visit_2858_);
lean_dec(v_root_2857_);
v___x_2862_ = lean_box(0);
return v___x_2862_;
}
else
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = lean_box(0);
v___x_2864_ = l___private_Lean_Syntax_0__Lean_Syntax_findStack_x3f_go(v_visit_2858_, v_accept_2859_, v___x_2863_, v_root_2857_);
return v___x_2864_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches___lam__0(uint8_t v___x_2865_, lean_object* v_x_2866_, lean_object* v_p_2867_){
_start:
{
if (lean_obj_tag(v_p_2867_) == 0)
{
lean_dec_ref(v_x_2866_);
return v___x_2865_;
}
else
{
lean_object* v_fst_2868_; lean_object* v_val_2869_; uint8_t v___x_2870_; 
v_fst_2868_ = lean_ctor_get(v_x_2866_, 0);
lean_inc(v_fst_2868_);
lean_dec_ref(v_x_2866_);
v_val_2869_ = lean_ctor_get(v_p_2867_, 0);
v___x_2870_ = l_Lean_Syntax_isOfKind(v_fst_2868_, v_val_2869_);
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___lam__0___boxed(lean_object* v___x_2871_, lean_object* v_x_2872_, lean_object* v_p_2873_){
_start:
{
uint8_t v___x_123__boxed_2874_; uint8_t v_res_2875_; lean_object* v_r_2876_; 
v___x_123__boxed_2874_ = lean_unbox(v___x_2871_);
v_res_2875_ = l_Lean_Syntax_Stack_matches___lam__0(v___x_123__boxed_2874_, v_x_2872_, v_p_2873_);
lean_dec(v_p_2873_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(lean_object* v_x_2877_){
_start:
{
if (lean_obj_tag(v_x_2877_) == 0)
{
uint8_t v___x_2878_; 
v___x_2878_ = 1;
return v___x_2878_;
}
else
{
lean_object* v_head_2879_; uint8_t v___x_2880_; 
v_head_2879_ = lean_ctor_get(v_x_2877_, 0);
v___x_2880_ = lean_unbox(v_head_2879_);
if (v___x_2880_ == 0)
{
uint8_t v___x_2881_; 
v___x_2881_ = lean_unbox(v_head_2879_);
return v___x_2881_;
}
else
{
lean_object* v_tail_2882_; 
v_tail_2882_ = lean_ctor_get(v_x_2877_, 1);
v_x_2877_ = v_tail_2882_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00Lean_Syntax_Stack_matches_spec__0___boxed(lean_object* v_x_2884_){
_start:
{
uint8_t v_res_2885_; lean_object* v_r_2886_; 
v_res_2885_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v_x_2884_);
lean_dec(v_x_2884_);
v_r_2886_ = lean_box(v_res_2885_);
return v_r_2886_;
}
}
LEAN_EXPORT uint8_t l_Lean_Syntax_Stack_matches(lean_object* v_stack_2889_, lean_object* v_pattern_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; uint8_t v___x_2893_; 
v___x_2891_ = l_List_lengthTR___redArg(v_pattern_2890_);
v___x_2892_ = l_List_lengthTR___redArg(v_stack_2889_);
v___x_2893_ = lean_nat_dec_le(v___x_2891_, v___x_2892_);
lean_dec(v___x_2892_);
lean_dec(v___x_2891_);
if (v___x_2893_ == 0)
{
lean_dec(v_pattern_2890_);
lean_dec(v_stack_2889_);
return v___x_2893_;
}
else
{
lean_object* v___x_2894_; lean_object* v___f_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2894_ = lean_box(v___x_2893_);
v___f_2895_ = lean_alloc_closure((void*)(l_Lean_Syntax_Stack_matches___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2895_, 0, v___x_2894_);
v___x_2896_ = ((lean_object*)(l_Lean_Syntax_Stack_matches___closed__0));
v___x_2897_ = l___private_Init_Data_List_Impl_0__List_zipWithTR_go(lean_box(0), lean_box(0), lean_box(0), v___f_2895_, v_stack_2889_, v_pattern_2890_, v___x_2896_);
v___x_2898_ = l_List_all___at___00Lean_Syntax_Stack_matches_spec__0(v___x_2897_);
lean_dec(v___x_2897_);
return v___x_2898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Stack_matches___boxed(lean_object* v_stack_2899_, lean_object* v_pattern_2900_){
_start:
{
uint8_t v_res_2901_; lean_object* v_r_2902_; 
v_res_2901_ = l_Lean_Syntax_Stack_matches(v_stack_2899_, v_pattern_2900_);
v_r_2902_ = lean_box(v_res_2901_);
return v_r_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing_x3f(lean_object* v_stx_2903_, lean_object* v_trailing_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Syntax_getTailInfo_x3f(v_stx_2903_);
if (lean_obj_tag(v___x_2905_) == 1)
{
lean_object* v_val_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2941_; 
v_val_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_2941_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_val_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2941_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
if (lean_obj_tag(v_val_2906_) == 0)
{
lean_object* v_trailing_2910_; lean_object* v_leading_2911_; lean_object* v_pos_2912_; lean_object* v_endPos_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2939_; 
v_trailing_2910_ = lean_ctor_get(v_val_2906_, 2);
v_leading_2911_ = lean_ctor_get(v_val_2906_, 0);
v_pos_2912_ = lean_ctor_get(v_val_2906_, 1);
v_endPos_2913_ = lean_ctor_get(v_val_2906_, 3);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_val_2906_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2915_ = v_val_2906_;
v_isShared_2916_ = v_isSharedCheck_2939_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_endPos_2913_);
lean_inc(v_trailing_2910_);
lean_inc(v_pos_2912_);
lean_inc(v_leading_2911_);
lean_dec(v_val_2906_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2939_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v_str_2917_; lean_object* v_startPos_2918_; lean_object* v_stopPos_2919_; lean_object* v_startPos_2920_; lean_object* v_stopPos_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2937_; 
v_str_2917_ = lean_ctor_get(v_trailing_2910_, 0);
lean_inc_ref(v_str_2917_);
v_startPos_2918_ = lean_ctor_get(v_trailing_2910_, 1);
lean_inc(v_startPos_2918_);
v_stopPos_2919_ = lean_ctor_get(v_trailing_2910_, 2);
lean_inc(v_stopPos_2919_);
lean_dec_ref(v_trailing_2910_);
v_startPos_2920_ = lean_ctor_get(v_trailing_2904_, 1);
v_stopPos_2921_ = lean_ctor_get(v_trailing_2904_, 2);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_trailing_2904_);
if (v_isSharedCheck_2937_ == 0)
{
lean_object* v_unused_2938_; 
v_unused_2938_ = lean_ctor_get(v_trailing_2904_, 0);
lean_dec(v_unused_2938_);
v___x_2923_ = v_trailing_2904_;
v_isShared_2924_ = v_isSharedCheck_2937_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_stopPos_2921_);
lean_inc(v_startPos_2920_);
lean_dec(v_trailing_2904_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2937_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
uint8_t v_decide_2925_; 
v_decide_2925_ = lean_nat_dec_eq(v_stopPos_2919_, v_startPos_2920_);
lean_dec(v_startPos_2920_);
lean_dec(v_stopPos_2919_);
if (v_decide_2925_ == 0)
{
lean_object* v___x_2926_; 
lean_del_object(v___x_2923_);
lean_dec(v_stopPos_2921_);
lean_dec(v_startPos_2918_);
lean_dec_ref(v_str_2917_);
lean_del_object(v___x_2915_);
lean_dec(v_endPos_2913_);
lean_dec(v_pos_2912_);
lean_dec_ref(v_leading_2911_);
lean_del_object(v___x_2908_);
lean_dec(v_stx_2903_);
v___x_2926_ = lean_box(0);
return v___x_2926_;
}
else
{
lean_object* v_trailing_2928_; 
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v_startPos_2918_);
lean_ctor_set(v___x_2923_, 0, v_str_2917_);
v_trailing_2928_ = v___x_2923_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_str_2917_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_startPos_2918_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_stopPos_2921_);
v_trailing_2928_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2930_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 2, v_trailing_2928_);
v___x_2930_ = v___x_2915_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_leading_2911_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_pos_2912_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_trailing_2928_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_endPos_2913_);
v___x_2930_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = l_Lean_Syntax_setTailInfo(v_stx_2903_, v___x_2930_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_2931_);
v___x_2933_ = v___x_2908_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2940_; 
lean_del_object(v___x_2908_);
lean_dec(v_val_2906_);
lean_dec_ref(v_trailing_2904_);
lean_dec(v_stx_2903_);
v___x_2940_ = lean_box(0);
return v___x_2940_;
}
}
}
else
{
lean_object* v___x_2942_; 
lean_dec(v___x_2905_);
lean_dec_ref(v_trailing_2904_);
lean_dec(v_stx_2903_);
v___x_2942_ = lean_box(0);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_addTrailing(lean_object* v_stx_2943_, lean_object* v_trailing_2944_){
_start:
{
lean_object* v___x_2945_; 
lean_inc(v_stx_2943_);
v___x_2945_ = l_Lean_Syntax_addTrailing_x3f(v_stx_2943_, v_trailing_2944_);
if (lean_obj_tag(v___x_2945_) == 0)
{
return v_stx_2943_;
}
else
{
lean_object* v_val_2946_; 
lean_dec(v_stx_2943_);
v_val_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_val_2946_);
lean_dec_ref_known(v___x_2945_, 1);
return v_val_2946_;
}
}
}
lean_object* runtime_initialize_Init_Data_Slice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Format(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Syntax(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Lean_Data_Format(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Coe(uint8_t builtin);
lean_object* initialize_Init_Data_String_Hashable(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Coe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
